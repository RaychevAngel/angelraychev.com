import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0033
import IrregularNine14P05C0034

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5460 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 69 168 22 297 361 425 297), lower := (rows 7 26 69 168 22 32 64 128 256), losses := [] }

theorem u5460 : Upper (D 5) (R 5) [6,24,65,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5460
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5461 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 168 25 294 358 422 294), lower := (rows 7 26 69 168 25 32 64 128 256), losses := [] }

theorem u5461 : Upper (D 5) (R 5) [6,24,65,160,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5461
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5462 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 168 26 293 357 421 293), lower := (rows 7 26 69 168 26 32 64 128 256), losses := [] }

theorem u5462 : Upper (D 5) (R 5) [6,24,65,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5462
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5463 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 357, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 69 168 28 291 355 419 291), lower := (rows 7 26 69 168 28 32 64 128 256), losses := [] }

theorem u5463 : Upper (D 5) (R 5) [6,24,65,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5463
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5464 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 69 168 49 302 334 398 270), lower := (rows 7 26 69 168 49 32 64 128 256), losses := [] }

theorem u5464 : Upper (D 5) (R 5) [6,24,65,160,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5464
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5465 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 168 50 301 333 397 269), lower := (rows 7 26 69 168 50 32 64 128 256), losses := [] }

theorem u5465 : Upper (D 5) (R 5) [6,24,65,160,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5465
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5466 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 69 168 52 299 331 395 267), lower := (rows 7 26 69 168 52 32 64 128 256), losses := [] }

theorem u5466 : Upper (D 5) (R 5) [6,24,65,160,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5466
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5467 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 168 56 295 327 391 263), lower := (rows 7 26 69 168 56 32 64 128 256), losses := [] }

theorem u5467 : Upper (D 5) (R 5) [6,24,65,160,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5467
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5468 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 168, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 69 168 273 46 110 174 302), lower := (rows 7 26 69 168 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 29 16 33 65 129 257), good := (rows 494 26 492 168 506 32 64 128 256) }] }

theorem u5468 : Upper (D 5) (R 5) [6,24,65,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5468
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5469 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 69 168 274 45 109 173 301), lower := (rows 7 26 69 168 274 32 64 128 256), losses := [] }

theorem u5469 : Upper (D 5) (R 5) [6,24,65,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5469
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5470 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 168, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 69 168 276 43 107 171 299), lower := (rows 7 26 69 168 276 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 13 16 33 65 129 257), good := (rows 491 26 489 168 282 32 64 128 256) }] }

theorem u5470 : Upper (D 5) (R 5) [6,24,65,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5470
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5471 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 168 280 39 103 167 295), lower := (rows 7 26 69 168 280 32 64 128 256), losses := [] }

theorem u5471 : Upper (D 5) (R 5) [6,24,65,160,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5471
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5472 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 69 168 304 47 79 143 271), lower := (rows 7 26 69 168 304 32 64 128 256), losses := [] }

theorem u5472 : Upper (D 5) (R 5) [6,24,65,160,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5472
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5473 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 69 392 19 44 108 172 300), lower := (rows 7 26 69 392 19 32 64 128 256), losses := [] }

theorem u5473 : Upper (D 5) (R 5) [6,24,65,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5473
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5474 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 426, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 392 21 42 106 170 298), lower := (rows 7 26 69 392 21 32 64 128 256), losses := [] }

theorem u5474 : Upper (D 5) (R 5) [6,24,65,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5474
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5475 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 69 392 22 41 105 169 297), lower := (rows 7 26 69 392 22 32 64 128 256), losses := [] }

theorem u5475 : Upper (D 5) (R 5) [6,24,65,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5475
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5476 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 392 25 38 102 166 294), lower := (rows 7 26 69 392 25 32 64 128 256), losses := [] }

theorem u5476 : Upper (D 5) (R 5) [6,24,65,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5476
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5477 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 392 26 37 101 165 293), lower := (rows 7 26 69 392 26 32 64 128 256), losses := [] }

theorem u5477 : Upper (D 5) (R 5) [6,24,65,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5477
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5478 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 101, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 69 392 28 35 99 163 291), lower := (rows 7 26 69 392 28 32 64 128 256), losses := [] }

theorem u5478 : Upper (D 5) (R 5) [6,24,65,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5478
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5479 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 424, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 69 392 49 46 110 174 302), lower := (rows 7 26 69 392 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 29 16 33 65 129 257), good := (rows 494 26 492 392 506 32 64 128 256) }] }

theorem u5479 : Upper (D 5) (R 5) [6,24,65,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5479
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5480 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 69 392 50 45 109 173 301), lower := (rows 7 26 69 392 50 32 64 128 256), losses := [] }

theorem u5480 : Upper (D 5) (R 5) [6,24,65,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5480
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5481 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 424, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 69 392 52 43 107 171 299), lower := (rows 7 26 69 392 52 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 13 16 33 65 129 257), good := (rows 491 26 489 392 58 32 64 128 256) }] }

theorem u5481 : Upper (D 5) (R 5) [6,24,65,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5481
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5482 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 392 56 39 103 167 295), lower := (rows 7 26 69 392 56 32 64 128 256), losses := [] }

theorem u5482 : Upper (D 5) (R 5) [6,24,65,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5482
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5483 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 26 76 41 19 420 484 420 420), lower := (rows 7 26 76 41 19 32 64 128 256), losses := [] }

theorem u5483 : Upper (D 5) (R 5) [6,24,72,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5483
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5484 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 76 41 21 418 482 418 418), lower := (rows 7 26 76 41 21 32 64 128 256), losses := [] }

theorem u5484 : Upper (D 5) (R 5) [6,24,72,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5484
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5485 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 76 41 22 417 481 417 417), lower := (rows 7 26 76 41 22 32 64 128 256), losses := [] }

theorem u5485 : Upper (D 5) (R 5) [6,24,72,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5485
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5486 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 76 41 49 422 454 390 390), lower := (rows 7 26 76 41 49 32 64 128 256), losses := [] }

theorem u5486 : Upper (D 5) (R 5) [6,24,72,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5486
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5487 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 76 41 50 421 453 389 389), lower := (rows 7 26 76 41 50 32 64 128 256), losses := [] }

theorem u5487 : Upper (D 5) (R 5) [6,24,72,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5487
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5488 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 76 41 52 419 451 387 387), lower := (rows 7 26 76 41 52 32 64 128 256), losses := [] }

theorem u5488 : Upper (D 5) (R 5) [6,24,72,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5488
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5489 : PairBound 9 := { available := 294, camps := [{ cop := 0, region := 432, targets := 8 },{ cop := 1, region := 356, targets := 1 }], pairs := [(2,0),(4,3)], upper := (rows 7 26 76 41 145 294 358 422 294), lower := (rows 7 26 76 41 145 32 64 128 256), losses := [] }

theorem u5489 : Upper (D 5) (R 5) [6,24,72,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5489
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5490 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 76 41 146 293 357 421 293), lower := (rows 7 26 76 41 146 32 64 128 256), losses := [] }

theorem u5490 : Upper (D 5) (R 5) [6,24,72,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5490
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5491 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 296, targets := 4 },{ cop := 0, region := 432, targets := 8 }], pairs := [(3,2),(4,3)], upper := (rows 7 26 76 41 148 291 355 419 291), lower := (rows 7 26 76 41 148 32 64 128 256), losses := [] }

theorem u5491 : Upper (D 5) (R 5) [6,24,72,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5491
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5492 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 76 41 176 295 327 391 263), lower := (rows 7 26 76 41 176 32 64 128 256), losses := [] }

theorem u5492 : Upper (D 5) (R 5) [6,24,72,33,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5492
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5493 : Route 9 := (fun mask => (mask,id))

def c5493 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5493 : Upper (D 5) (R 5) [6,24,72,33,384] 13 := by
  apply FastRouting.sound _ _ [6,24,72,33,384] 13 (by decide) (choices 1) [1,2,4] r5493 c5493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2038
  · exact u2039
  · exact u2040

def b5494 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 26 76 137 19 292 356 420 292), lower := (rows 7 26 76 137 19 32 64 128 256), losses := [] }

theorem u5494 : Upper (D 5) (R 5) [6,24,72,129,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5494
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5495 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 76 137 21 290 354 418 290), lower := (rows 7 26 76 137 21 32 64 128 256), losses := [] }

theorem u5495 : Upper (D 5) (R 5) [6,24,72,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5495
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5496 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 76 137 22 289 353 417 289), lower := (rows 7 26 76 137 22 32 64 128 256), losses := [] }

theorem u5496 : Upper (D 5) (R 5) [6,24,72,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5496
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5497 : PairBound 9 := { available := 294, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 1, region := 356, targets := 1 }], pairs := [(2,0),(4,3)], upper := (rows 7 26 76 137 49 294 358 422 294), lower := (rows 7 26 76 137 49 32 64 128 256), losses := [] }

theorem u5497 : Upper (D 5) (R 5) [6,24,72,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5497
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5498 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 76 137 50 293 357 421 293), lower := (rows 7 26 76 137 50 32 64 128 256), losses := [] }

theorem u5498 : Upper (D 5) (R 5) [6,24,72,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5498
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5499 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 424, targets := 4 },{ cop := 0, region := 304, targets := 8 }], pairs := [(3,2),(4,3)], upper := (rows 7 26 76 137 52 291 355 419 291), lower := (rows 7 26 76 137 52 32 64 128 256), losses := [] }

theorem u5499 : Upper (D 5) (R 5) [6,24,72,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5499
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5500 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 1, region := 100, targets := 1 }], pairs := [(2,0),(4,3)], upper := (rows 7 26 76 137 273 38 102 166 294), lower := (rows 7 26 76 137 273 32 64 128 256), losses := [] }

theorem u5500 : Upper (D 5) (R 5) [6,24,72,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5500
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5501 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 76 137 274 37 101 165 293), lower := (rows 7 26 76 137 274 32 64 128 256), losses := [] }

theorem u5501 : Upper (D 5) (R 5) [6,24,72,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5501
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5502 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 168, targets := 4 },{ cop := 0, region := 304, targets := 8 }], pairs := [(3,2),(4,3)], upper := (rows 7 26 76 137 276 35 99 163 291), lower := (rows 7 26 76 137 276 32 64 128 256), losses := [] }

theorem u5502 : Upper (D 5) (R 5) [6,24,72,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5502
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5503 : Route 9 := (fun mask => (mask,id))

def c5503 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5503 : Upper (D 5) (R 5) [6,24,72,129,288] 13 := by
  apply FastRouting.sound _ _ [6,24,72,129,288] 13 (by decide) (choices 1) [1,2,4] r5503 c5503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2041
  · exact u2042
  · exact u2043

def b5504 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 76 168 19 293 357 421 293), lower := (rows 7 26 76 168 19 32 64 128 256), losses := [] }

theorem u5504 : Upper (D 5) (R 5) [6,24,72,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5504
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5505 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 76 168 21 291 355 419 291), lower := (rows 7 26 76 168 21 32 64 128 256), losses := [] }

theorem u5505 : Upper (D 5) (R 5) [6,24,72,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5505
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5506 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 76 168 22 289 353 417 289), lower := (rows 7 26 76 168 22 32 64 128 256), losses := [] }

theorem u5506 : Upper (D 5) (R 5) [6,24,72,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5506
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5507 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 76 168 49 295 327 391 263), lower := (rows 7 26 76 168 49 32 64 128 256), losses := [] }

theorem u5507 : Upper (D 5) (R 5) [6,24,72,160,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5507
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5508 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 76 168 50 293 325 389 261), lower := (rows 7 26 76 168 50 32 64 128 256), losses := [] }

theorem u5508 : Upper (D 5) (R 5) [6,24,72,160,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5508
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5509 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 76 168 52 291 323 387 259), lower := (rows 7 26 76 168 52 32 64 128 256), losses := [] }

theorem u5509 : Upper (D 5) (R 5) [6,24,72,160,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5509
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5510 : Route 9 := (fun mask => (mask,id))

def c5510 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5510 : Upper (D 5) (R 5) [6,24,72,160,257] 13 := by
  apply FastRouting.sound _ _ [6,24,72,160,257] 13 (by decide) (choices 1) [1,2,4] r5510 c5510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2044
  · exact u2045
  · exact u2046

def b5511 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 76 168 274 37 101 165 293), lower := (rows 7 26 76 168 274 32 64 128 256), losses := [] }

theorem u5511 : Upper (D 5) (R 5) [6,24,72,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5511
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5512 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 168, targets := 4 },{ cop := 0, region := 304, targets := 8 }], pairs := [(3,2),(4,3)], upper := (rows 7 26 76 168 276 35 99 163 291), lower := (rows 7 26 76 168 276 32 64 128 256), losses := [] }

theorem u5512 : Upper (D 5) (R 5) [6,24,72,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5512
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5513 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 76 168 304 39 71 135 263), lower := (rows 7 26 76 168 304 32 64 128 256), losses := [] }

theorem u5513 : Upper (D 5) (R 5) [6,24,72,160,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5513
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5514 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 76 392 19 37 101 165 293), lower := (rows 7 26 76 392 19 32 64 128 256), losses := [] }

theorem u5514 : Upper (D 5) (R 5) [6,24,72,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5514
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5515 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 76 392 21 35 99 163 291), lower := (rows 7 26 76 392 21 32 64 128 256), losses := [] }

theorem u5515 : Upper (D 5) (R 5) [6,24,72,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5515
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5516 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 76 392 22 33 97 161 289), lower := (rows 7 26 76 392 22 32 64 128 256), losses := [] }

theorem u5516 : Upper (D 5) (R 5) [6,24,72,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5516
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5517 : Route 9 := (fun mask => (mask,id))

def c5517 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5517 : Upper (D 5) (R 5) [6,24,72,384,33] 13 := by
  apply FastRouting.sound _ _ [6,24,72,384,33] 13 (by decide) (choices 1) [1,2,4] r5517 c5517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2047
  · exact u2048
  · exact u2049

def b5518 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 76 392 50 37 101 165 293), lower := (rows 7 26 76 392 50 32 64 128 256), losses := [] }

theorem u5518 : Upper (D 5) (R 5) [6,24,72,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5518
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5519 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 424, targets := 4 },{ cop := 0, region := 48, targets := 8 }], pairs := [(3,2),(4,3)], upper := (rows 7 26 76 392 52 35 99 163 291), lower := (rows 7 26 76 392 52 32 64 128 256), losses := [] }

theorem u5519 : Upper (D 5) (R 5) [6,24,72,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5519
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u5519
end Delivery.IrregularNine14.P05
