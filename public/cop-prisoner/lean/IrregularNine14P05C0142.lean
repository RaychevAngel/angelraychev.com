import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0083

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8520 : PairBound 9 := { available := 299, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 196 56 315 299 363 427 299), lower := (rows 7 7 196 56 16 32 64 128 256), losses := [] }

theorem u8520 : Upper (D 5) (R 5) [6,5,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8520
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8521 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 196 265 58 58 122 186 314), lower := (rows 7 7 196 265 16 32 64 128 256), losses := [] }

theorem u8521 : Upper (D 5) (R 5) [6,5,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8521
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8522 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 196 280 59 43 107 171 299), lower := (rows 7 7 196 280 16 32 64 128 256), losses := [] }

theorem u8522 : Upper (D 5) (R 5) [6,5,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8522
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8523 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 196 296 59 59 123 187 315), lower := (rows 7 7 196 296 16 32 64 128 256), losses := [] }

theorem u8523 : Upper (D 5) (R 5) [6,5,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8523
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8524 : PairBound 9 := { available := 486, camps := [{ cop := 3, region := 7, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 13 56 502 486 486 486 486), lower := (rows 7 11 13 56 16 32 64 128 256), losses := [] }

theorem u8524 : Upper (D 5) (R 5) [6,9,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8524
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8525 : PairBound 9 := { available := 422, camps := [{ cop := 3, region := 7, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 13 88 438 422 486 422 422), lower := (rows 7 11 13 88 16 32 64 128 256), losses := [] }

theorem u8525 : Upper (D 5) (R 5) [6,9,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8525
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8526 : PairBound 9 := { available := 438, camps := [{ cop := 3, region := 7, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 13 104 438 438 502 438 438), lower := (rows 7 11 13 104 16 32 64 128 256), losses := [] }

theorem u8526 : Upper (D 5) (R 5) [6,9,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8526
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8527 : PairBound 9 := { available := 310, camps := [{ cop := 3, region := 7, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 13 200 310 310 374 438 310), lower := (rows 7 11 13 200 16 32 64 128 256), losses := [] }

theorem u8527 : Upper (D 5) (R 5) [6,9,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8527
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8528 : PairBound 9 := { available := 485, camps := [{ cop := 3, region := 7, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 14 56 501 485 485 485 485), lower := (rows 7 11 14 56 16 32 64 128 256), losses := [] }

theorem u8528 : Upper (D 5) (R 5) [6,9,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8528
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8529 : PairBound 9 := { available := 421, camps := [{ cop := 3, region := 7, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 14 88 437 421 485 421 421), lower := (rows 7 11 14 88 16 32 64 128 256), losses := [] }

theorem u8529 : Upper (D 5) (R 5) [6,9,10,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8529
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8530 : PairBound 9 := { available := 437, camps := [{ cop := 3, region := 7, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 14 104 437 437 501 437 437), lower := (rows 7 11 14 104 16 32 64 128 256), losses := [] }

theorem u8530 : Upper (D 5) (R 5) [6,9,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8530
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8531 : PairBound 9 := { available := 309, camps := [{ cop := 3, region := 7, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 14 200 309 309 373 437 309), lower := (rows 7 11 14 200 16 32 64 128 256), losses := [] }

theorem u8531 : Upper (D 5) (R 5) [6,9,10,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8531
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8532 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 21 44 506 490 490 490 490), lower := (rows 7 11 21 44 16 32 64 128 256), losses := [] }

theorem u8532 : Upper (D 5) (R 5) [6,9,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8532
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8533 : PairBound 9 := { available := 426, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 21 76 442 426 490 426 426), lower := (rows 7 11 21 76 16 32 64 128 256), losses := [] }

theorem u8533 : Upper (D 5) (R 5) [6,9,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8533
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8534 : PairBound 9 := { available := 430, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 21 104 446 430 494 430 430), lower := (rows 7 11 21 104 16 32 64 128 256), losses := [] }

theorem u8534 : Upper (D 5) (R 5) [6,9,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8534
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8535 : PairBound 9 := { available := 302, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 21 200 318 302 366 430 302), lower := (rows 7 11 21 200 16 32 64 128 256), losses := [] }

theorem u8535 : Upper (D 5) (R 5) [6,9,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8535
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8536 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 22 44 505 489 489 489 489), lower := (rows 7 11 22 44 16 32 64 128 256), losses := [] }

theorem u8536 : Upper (D 5) (R 5) [6,9,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8536
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8537 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 22 76 441 425 489 425 425), lower := (rows 7 11 22 76 16 32 64 128 256), losses := [] }

theorem u8537 : Upper (D 5) (R 5) [6,9,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8537
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8538 : PairBound 9 := { available := 429, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 22 104 445 429 493 429 429), lower := (rows 7 11 22 104 16 32 64 128 256), losses := [] }

theorem u8538 : Upper (D 5) (R 5) [6,9,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8538
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8539 : PairBound 9 := { available := 301, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 22 200 317 301 365 429 301), lower := (rows 7 11 22 200 16 32 64 128 256), losses := [] }

theorem u8539 : Upper (D 5) (R 5) [6,9,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8539
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8540 : PairBound 9 := { available := 486, camps := [{ cop := 1, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 11 28 41 502 486 486 486 486), lower := (rows 7 11 28 41 16 32 64 128 256), losses := [] }

theorem u8540 : Upper (D 5) (R 5) [6,9,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8540
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8541 : PairBound 9 := { available := 485, camps := [{ cop := 0, region := 496, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 11 28 42 501 485 485 485 485), lower := (rows 7 11 28 42 16 32 64 128 256), losses := [] }

theorem u8541 : Upper (D 5) (R 5) [6,9,24,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8541
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8542 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 496, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 11 28 44 499 483 483 483 483), lower := (rows 7 11 28 44 16 32 64 128 256), losses := [] }

theorem u8542 : Upper (D 5) (R 5) [6,9,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8542
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8543 : PairBound 9 := { available := 422, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 11 28 73 438 422 486 422 422), lower := (rows 7 11 28 73 16 32 64 128 256), losses := [] }

theorem u8543 : Upper (D 5) (R 5) [6,9,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8543
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8544 : PairBound 9 := { available := 421, camps := [{ cop := 0, region := 432, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 11 28 74 437 421 485 421 421), lower := (rows 7 11 28 74 16 32 64 128 256), losses := [] }

theorem u8544 : Upper (D 5) (R 5) [6,9,24,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8544
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8545 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 432, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 11 28 76 435 419 483 419 419), lower := (rows 7 11 28 76 16 32 64 128 256), losses := [] }

theorem u8545 : Upper (D 5) (R 5) [6,9,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8545
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8546 : PairBound 9 := { available := 423, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 28 104 439 423 487 423 423), lower := (rows 7 11 28 104 16 32 64 128 256), losses := [] }

theorem u8546 : Upper (D 5) (R 5) [6,9,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8546
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8547 : PairBound 9 := { available := 295, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 28 200 311 295 359 423 295), lower := (rows 7 11 28 200 16 32 64 128 256), losses := [] }

theorem u8547 : Upper (D 5) (R 5) [6,9,24,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8547
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8548 : PairBound 9 := { available := 462, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 56 478 494 462 462 462), lower := (rows 7 11 37 56 16 32 64 128 256), losses := [] }

theorem u8548 : Upper (D 5) (R 5) [6,9,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8548
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8549 : PairBound 9 := { available := 442, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 76 442 442 506 442 442), lower := (rows 7 11 37 76 16 32 64 128 256), losses := [] }

theorem u8549 : Upper (D 5) (R 5) [6,9,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8549
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8550 : PairBound 9 := { available := 430, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 88 446 430 494 430 430), lower := (rows 7 11 37 88 16 32 64 128 256), losses := [] }

theorem u8550 : Upper (D 5) (R 5) [6,9,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8550
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8551 : PairBound 9 := { available := 414, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 104 414 446 478 414 414), lower := (rows 7 11 37 104 16 32 64 128 256), losses := [] }

theorem u8551 : Upper (D 5) (R 5) [6,9,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8551
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8552 : PairBound 9 := { available := 318, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 200 318 318 382 446 318), lower := (rows 7 11 37 200 16 32 64 128 256), losses := [] }

theorem u8552 : Upper (D 5) (R 5) [6,9,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8552
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8553 : PairBound 9 := { available := 461, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 38 56 477 493 461 461 461), lower := (rows 7 11 38 56 16 32 64 128 256), losses := [] }

theorem u8553 : Upper (D 5) (R 5) [6,9,34,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8553
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8554 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 38 76 441 441 505 441 441), lower := (rows 7 11 38 76 16 32 64 128 256), losses := [] }

theorem u8554 : Upper (D 5) (R 5) [6,9,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8554
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8555 : PairBound 9 := { available := 429, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 38 88 445 429 493 429 429), lower := (rows 7 11 38 88 16 32 64 128 256), losses := [] }

theorem u8555 : Upper (D 5) (R 5) [6,9,34,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8555
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8556 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 38 104 413 445 477 413 413), lower := (rows 7 11 38 104 16 32 64 128 256), losses := [] }

theorem u8556 : Upper (D 5) (R 5) [6,9,34,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8556
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8557 : PairBound 9 := { available := 317, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 38 200 317 317 381 445 317), lower := (rows 7 11 38 200 16 32 64 128 256), losses := [] }

theorem u8557 : Upper (D 5) (R 5) [6,9,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8557
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8558 : PairBound 9 := { available := 455, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 44 56 471 487 455 455 455), lower := (rows 7 11 44 56 16 32 64 128 256), losses := [] }

theorem u8558 : Upper (D 5) (R 5) [6,9,40,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8558
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8559 : PairBound 9 := { available := 438, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 11 44 73 438 438 502 438 438), lower := (rows 7 11 44 73 16 32 64 128 256), losses := [] }

theorem u8559 : Upper (D 5) (R 5) [6,9,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8559
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8560 : PairBound 9 := { available := 437, camps := [{ cop := 0, region := 432, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 11 44 74 437 437 501 437 437), lower := (rows 7 11 44 74 16 32 64 128 256), losses := [] }

theorem u8560 : Upper (D 5) (R 5) [6,9,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8560
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8561 : PairBound 9 := { available := 435, camps := [{ cop := 0, region := 432, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 11 44 76 435 435 499 435 435), lower := (rows 7 11 44 76 16 32 64 128 256), losses := [] }

theorem u8561 : Upper (D 5) (R 5) [6,9,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8561
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8562 : PairBound 9 := { available := 423, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 44 88 439 423 487 423 423), lower := (rows 7 11 44 88 16 32 64 128 256), losses := [] }

theorem u8562 : Upper (D 5) (R 5) [6,9,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8562
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8563 : PairBound 9 := { available := 407, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 44 104 407 439 471 407 407), lower := (rows 7 11 44 104 16 32 64 128 256), losses := [] }

theorem u8563 : Upper (D 5) (R 5) [6,9,40,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8563
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8564 : PairBound 9 := { available := 311, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 44 200 311 311 375 439 311), lower := (rows 7 11 44 200 16 32 64 128 256), losses := [] }

theorem u8564 : Upper (D 5) (R 5) [6,9,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8564
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8565 : PairBound 9 := { available := 430, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 11 52 73 446 430 494 430 430), lower := (rows 7 11 52 73 16 32 64 128 256), losses := [] }

theorem u8565 : Upper (D 5) (R 5) [6,9,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8565
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8566 : PairBound 9 := { available := 429, camps := [{ cop := 1, region := 436, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 11 52 74 445 429 493 429 429), lower := (rows 7 11 52 74 16 32 64 128 256), losses := [] }

theorem u8566 : Upper (D 5) (R 5) [6,9,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8566
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8567 : PairBound 9 := { available := 427, camps := [{ cop := 3, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 52 76 443 427 491 427 427), lower := (rows 7 11 52 76 16 32 64 128 256), losses := [] }

theorem u8567 : Upper (D 5) (R 5) [6,9,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8567
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8568 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8568 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8568 : Upper (D 5) (R 5) [6,9,48,96] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136,384] r8568 c8568
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u4990
  · exact u4991
  · exact u4992
  · exact u4993
  · exact u4994
  · exact u4995
  · exact u4996
  · exact u4997
  · exact u4998
  · exact u4999
  · exact u5000

def r8569 : Route 9 := (fun mask => (mask,id))

def c8569 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8569 : Upper (D 5) (R 5) [6,9,48,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r8569 c8569
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5001
  · exact u5002
  · exact u5003
  · exact u5004
  · exact u5005
  · exact u5006
  · exact u5007
  · exact u5008
  · exact u5009
  · exact u5010
  · exact u5011
  · exact u5012
  · exact u5013
  · exact u5014
  · exact u5015

def b8570 : PairBound 9 := { available := 314, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 69 140 314 314 378 442 314), lower := (rows 7 11 69 140 16 32 64 128 256), losses := [] }

theorem u8570 : Upper (D 5) (R 5) [6,9,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8570
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8571 : PairBound 9 := { available := 302, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 69 152 318 302 366 430 302), lower := (rows 7 11 69 152 16 32 64 128 256), losses := [] }

theorem u8571 : Upper (D 5) (R 5) [6,9,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8571
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8572 : PairBound 9 := { available := 318, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 69 168 318 318 382 446 318), lower := (rows 7 11 69 168 16 32 64 128 256), losses := [] }

theorem u8572 : Upper (D 5) (R 5) [6,9,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8572
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8573 : PairBound 9 := { available := 62, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 69 392 62 62 126 190 318), lower := (rows 7 11 69 392 16 32 64 128 256), losses := [] }

theorem u8573 : Upper (D 5) (R 5) [6,9,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8573
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8574 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 70 140 313 313 377 441 313), lower := (rows 7 11 70 140 16 32 64 128 256), losses := [] }

theorem u8574 : Upper (D 5) (R 5) [6,9,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8574
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8575 : PairBound 9 := { available := 301, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 70 152 317 301 365 429 301), lower := (rows 7 11 70 152 16 32 64 128 256), losses := [] }

theorem u8575 : Upper (D 5) (R 5) [6,9,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8575
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8576 : PairBound 9 := { available := 317, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 70 168 317 317 381 445 317), lower := (rows 7 11 70 168 16 32 64 128 256), losses := [] }

theorem u8576 : Upper (D 5) (R 5) [6,9,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8576
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8577 : PairBound 9 := { available := 61, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 70 392 61 61 125 189 317), lower := (rows 7 11 70 392 16 32 64 128 256), losses := [] }

theorem u8577 : Upper (D 5) (R 5) [6,9,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8577
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8578 : PairBound 9 := { available := 307, camps := [{ cop := 0, region := 304, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 11 76 140 307 307 371 435 307), lower := (rows 7 11 76 140 16 32 64 128 256), losses := [] }

theorem u8578 : Upper (D 5) (R 5) [6,9,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8578
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8579 : PairBound 9 := { available := 295, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 76 152 311 295 359 423 295), lower := (rows 7 11 76 152 16 32 64 128 256), losses := [] }

theorem u8579 : Upper (D 5) (R 5) [6,9,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8579
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u8579
end Delivery.IrregularNine14.P05
