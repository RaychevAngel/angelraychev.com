import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0084
import IrregularNine14P05C0085

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8640 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 76 56 435 419 483 419 419), lower := (rows 7 14 76 56 16 32 64 128 256), losses := [] }

theorem u8640 : Upper (D 5) (R 5) [6,12,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8640
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8641 : PairBound 9 := { available := 307, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 76 137 307 307 371 435 307), lower := (rows 7 14 76 137 16 32 64 128 256), losses := [] }

theorem u8641 : Upper (D 5) (R 5) [6,12,72,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8641
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8642 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 76 152 307 291 355 419 291), lower := (rows 7 14 76 152 16 32 64 128 256), losses := [] }

theorem u8642 : Upper (D 5) (R 5) [6,12,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8642
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8643 : PairBound 9 := { available := 307, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 76 168 307 307 371 435 307), lower := (rows 7 14 76 168 16 32 64 128 256), losses := [] }

theorem u8643 : Upper (D 5) (R 5) [6,12,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8643
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8644 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 76 392 51 51 115 179 307), lower := (rows 7 14 76 392 16 32 64 128 256), losses := [] }

theorem u8644 : Upper (D 5) (R 5) [6,12,72,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8644
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8645 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 84 41 443 427 491 427 427), lower := (rows 7 14 84 41 16 32 64 128 256), losses := [] }

theorem u8645 : Upper (D 5) (R 5) [6,12,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8645
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8646 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 84 42 441 425 489 425 425), lower := (rows 7 14 84 42 16 32 64 128 256), losses := [] }

theorem u8646 : Upper (D 5) (R 5) [6,12,80,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8646
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8647 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 84 137 315 299 363 427 299), lower := (rows 7 14 84 137 16 32 64 128 256), losses := [] }

theorem u8647 : Upper (D 5) (R 5) [6,12,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8647
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8648 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 84 138 313 297 361 425 297), lower := (rows 7 14 84 138 16 32 64 128 256), losses := [] }

theorem u8648 : Upper (D 5) (R 5) [6,12,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8648
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8649 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 84 168 315 299 363 427 299), lower := (rows 7 14 84 168 16 32 64 128 256), losses := [] }

theorem u8649 : Upper (D 5) (R 5) [6,12,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8649
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8650 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 84 392 59 43 107 171 299), lower := (rows 7 14 84 392 16 32 64 128 256), losses := [] }

theorem u8650 : Upper (D 5) (R 5) [6,12,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8650
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8651 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 100 25 443 427 491 427 427), lower := (rows 7 14 100 25 16 32 64 128 256), losses := [] }

theorem u8651 : Upper (D 5) (R 5) [6,12,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8651
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8652 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 100 26 441 425 489 425 425), lower := (rows 7 14 100 26 16 32 64 128 256), losses := [] }

theorem u8652 : Upper (D 5) (R 5) [6,12,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8652
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8653 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 100 41 411 443 475 411 411), lower := (rows 7 14 100 41 16 32 64 128 256), losses := [] }

theorem u8653 : Upper (D 5) (R 5) [6,12,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8653
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8654 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 100 56 411 427 459 395 395), lower := (rows 7 14 100 56 16 32 64 128 256), losses := [] }

theorem u8654 : Upper (D 5) (R 5) [6,12,96,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8654
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8655 : PairBound 9 := { available := 315, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 100 137 315 315 379 443 315), lower := (rows 7 14 100 137 16 32 64 128 256), losses := [] }

theorem u8655 : Upper (D 5) (R 5) [6,12,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8655
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8656 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 100 138 313 313 377 441 313), lower := (rows 7 14 100 138 16 32 64 128 256), losses := [] }

theorem u8656 : Upper (D 5) (R 5) [6,12,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8656
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8657 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 100 152 315 299 363 427 299), lower := (rows 7 14 100 152 16 32 64 128 256), losses := [] }

theorem u8657 : Upper (D 5) (R 5) [6,12,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8657
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8658 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 100 168 283 315 347 411 283), lower := (rows 7 14 100 168 16 32 64 128 256), losses := [] }

theorem u8658 : Upper (D 5) (R 5) [6,12,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8658
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8659 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 100 392 59 59 123 187 315), lower := (rows 7 14 100 392 16 32 64 128 256), losses := [] }

theorem u8659 : Upper (D 5) (R 5) [6,12,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8659
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8660 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 196 25 315 299 363 427 299), lower := (rows 7 14 196 25 16 32 64 128 256), losses := [] }

theorem u8660 : Upper (D 5) (R 5) [6,12,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8660
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8661 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 196 26 313 297 361 425 297), lower := (rows 7 14 196 26 16 32 64 128 256), losses := [] }

theorem u8661 : Upper (D 5) (R 5) [6,12,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8661
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8662 : PairBound 9 := { available := 315, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 196 41 315 315 379 443 315), lower := (rows 7 14 196 41 16 32 64 128 256), losses := [] }

theorem u8662 : Upper (D 5) (R 5) [6,12,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8662
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8663 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 196 42 313 313 377 441 313), lower := (rows 7 14 196 42 16 32 64 128 256), losses := [] }

theorem u8663 : Upper (D 5) (R 5) [6,12,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8663
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8664 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 196 56 315 299 363 427 299), lower := (rows 7 14 196 56 16 32 64 128 256), losses := [] }

theorem u8664 : Upper (D 5) (R 5) [6,12,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8664
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8665 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 196 265 59 59 123 187 315), lower := (rows 7 14 196 265 16 32 64 128 256), losses := [] }

theorem u8665 : Upper (D 5) (R 5) [6,12,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8665
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8666 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 196 266 57 57 121 185 313), lower := (rows 7 14 196 266 16 32 64 128 256), losses := [] }

theorem u8666 : Upper (D 5) (R 5) [6,12,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8666
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8667 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 196 280 59 43 107 171 299), lower := (rows 7 14 196 280 16 32 64 128 256), losses := [] }

theorem u8667 : Upper (D 5) (R 5) [6,12,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8667
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8668 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 196 296 59 59 123 187 315), lower := (rows 7 14 196 296 16 32 64 128 256), losses := [] }

theorem u8668 : Upper (D 5) (R 5) [6,12,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8668
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8669 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 496, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 37 14 504 488 488 488 488), lower := (rows 7 19 37 14 16 32 64 128 256), losses := [] }

theorem u8669 : Upper (D 5) (R 5) [6,17,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8669
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8670 : PairBound 9 := { available := 460, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 37 42 476 492 460 460 460), lower := (rows 7 19 37 42 16 32 64 128 256), losses := [] }

theorem u8670 : Upper (D 5) (R 5) [6,17,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8670
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8671 : PairBound 9 := { available := 428, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 37 74 444 428 492 428 428), lower := (rows 7 19 37 74 16 32 64 128 256), losses := [] }

theorem u8671 : Upper (D 5) (R 5) [6,17,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8671
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8672 : PairBound 9 := { available := 426, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 37 76 442 426 490 426 426), lower := (rows 7 19 37 76 16 32 64 128 256), losses := [] }

theorem u8672 : Upper (D 5) (R 5) [6,17,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8672
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8673 : PairBound 9 := { available := 398, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 37 104 414 430 462 398 398), lower := (rows 7 19 37 104 16 32 64 128 256), losses := [] }

theorem u8673 : Upper (D 5) (R 5) [6,17,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8673
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8674 : PairBound 9 := { available := 302, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 37 200 318 302 366 430 302), lower := (rows 7 19 37 200 16 32 64 128 256), losses := [] }

theorem u8674 : Upper (D 5) (R 5) [6,17,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8674
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8675 : PairBound 9 := { available := 460, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 38 41 476 492 460 460 460), lower := (rows 7 19 38 41 16 32 64 128 256), losses := [] }

theorem u8675 : Upper (D 5) (R 5) [6,17,34,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8675
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8676 : PairBound 9 := { available := 428, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 38 73 444 428 492 428 428), lower := (rows 7 19 38 73 16 32 64 128 256), losses := [] }

theorem u8676 : Upper (D 5) (R 5) [6,17,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8676
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8677 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 38 76 441 425 489 425 425), lower := (rows 7 19 38 76 16 32 64 128 256), losses := [] }

theorem u8677 : Upper (D 5) (R 5) [6,17,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8677
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8678 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 38 104 413 429 461 397 397), lower := (rows 7 19 38 104 16 32 64 128 256), losses := [] }

theorem u8678 : Upper (D 5) (R 5) [6,17,34,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8678
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8679 : PairBound 9 := { available := 301, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 38 200 317 301 365 429 301), lower := (rows 7 19 38 200 16 32 64 128 256), losses := [] }

theorem u8679 : Upper (D 5) (R 5) [6,17,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8679
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8680 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 19 44 14 505 489 489 489 489), lower := (rows 7 19 44 14 16 32 64 128 256), losses := [] }

theorem u8680 : Upper (D 5) (R 5) [6,17,40,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8680
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8681 : PairBound 9 := { available := 462, camps := [{ cop := 2, region := 467, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 44 41 478 494 462 462 462), lower := (rows 7 19 44 41 16 32 64 128 256), losses := [] }

theorem u8681 : Upper (D 5) (R 5) [6,17,40,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8681
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8682 : PairBound 9 := { available := 461, camps := [{ cop := 2, region := 467, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 44 42 477 493 461 461 461), lower := (rows 7 19 44 42 16 32 64 128 256), losses := [] }

theorem u8682 : Upper (D 5) (R 5) [6,17,40,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8682
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8683 : PairBound 9 := { available := 459, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 44 44 475 491 459 459 459), lower := (rows 7 19 44 44 16 32 64 128 256), losses := [] }

theorem u8683 : Upper (D 5) (R 5) [6,17,40,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8683
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8684 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8684 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8684 : Upper (D 5) (R 5) [6,17,40,65] 13 := by
  apply FastRouting.sound _ _ [6,17,40,65] 13 (by decide) (choices 2) [6,10,12,34,36,40,130,132,136,160,384] r8684 c8684
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5057
  · exact u5058
  · exact u5059
  · exact u5060
  · exact u5061
  · exact u5062
  · exact u5063
  · exact u5064
  · exact u5065
  · exact u5066
  · exact u5067

def r8685 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8685 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8685 : Upper (D 5) (R 5) [6,17,40,66] 13 := by
  apply FastRouting.sound _ _ [6,17,40,66] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160,384] r8685 c8685
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5068
  · exact u5069
  · exact u5070
  · exact u5071
  · exact u5072
  · exact u5073
  · exact u5074
  · exact u5075
  · exact u5076
  · exact u5077
  · exact u5078

def r8686 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8686 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8686 : Upper (D 5) (R 5) [6,17,40,68] 13 := by
  apply FastRouting.sound _ _ [6,17,40,68] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160,384] r8686 c8686
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5079
  · exact u5080
  · exact u5081
  · exact u5082
  · exact u5083
  · exact u5084
  · exact u5085
  · exact u5086
  · exact u5087
  · exact u5088
  · exact u5089

def b8687 : PairBound 9 := { available := 399, camps := [{ cop := 2, region := 403, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 44 104 415 431 463 399 399), lower := (rows 7 19 44 104 16 32 64 128 256), losses := [] }

theorem u8687 : Upper (D 5) (R 5) [6,17,40,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8687
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8688 : Route 9 := (fun mask => (mask,id))

def c8688 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8688 : Upper (D 5) (R 5) [6,17,40,192] 13 := by
  apply FastRouting.sound _ _ [6,17,40,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r8688 c8688
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5090
  · exact u5091
  · exact u5092
  · exact u5093
  · exact u5094
  · exact u5095
  · exact u5096
  · exact u5097
  · exact u5098
  · exact u5099
  · exact u5100
  · exact u5101
  · exact u5102
  · exact u5103
  · exact u5104

def b8689 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 432, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 69 14 440 424 488 424 424), lower := (rows 7 19 69 14 16 32 64 128 256), losses := [] }

theorem u8689 : Upper (D 5) (R 5) [6,17,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8689
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8690 : PairBound 9 := { available := 428, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 69 42 444 428 492 428 428), lower := (rows 7 19 69 42 16 32 64 128 256), losses := [] }

theorem u8690 : Upper (D 5) (R 5) [6,17,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8690
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8691 : PairBound 9 := { available := 426, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 69 44 442 426 490 426 426), lower := (rows 7 19 69 44 16 32 64 128 256), losses := [] }

theorem u8691 : Upper (D 5) (R 5) [6,17,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8691
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8692 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 69 138 316 300 364 428 300), lower := (rows 7 19 69 138 16 32 64 128 256), losses := [] }

theorem u8692 : Upper (D 5) (R 5) [6,17,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8692
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8693 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 69 140 314 298 362 426 298), lower := (rows 7 19 69 140 16 32 64 128 256), losses := [] }

theorem u8693 : Upper (D 5) (R 5) [6,17,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8693
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8694 : PairBound 9 := { available := 302, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 69 168 318 302 366 430 302), lower := (rows 7 19 69 168 16 32 64 128 256), losses := [] }

theorem u8694 : Upper (D 5) (R 5) [6,17,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8694
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8695 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 69 392 62 46 110 174 302), lower := (rows 7 19 69 392 16 32 64 128 256), losses := [] }

theorem u8695 : Upper (D 5) (R 5) [6,17,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8695
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8696 : PairBound 9 := { available := 428, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 70 41 444 428 492 428 428), lower := (rows 7 19 70 41 16 32 64 128 256), losses := [] }

theorem u8696 : Upper (D 5) (R 5) [6,17,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8696
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8697 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 70 44 441 425 489 425 425), lower := (rows 7 19 70 44 16 32 64 128 256), losses := [] }

theorem u8697 : Upper (D 5) (R 5) [6,17,66,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8697
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8698 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 70 137 316 300 364 428 300), lower := (rows 7 19 70 137 16 32 64 128 256), losses := [] }

theorem u8698 : Upper (D 5) (R 5) [6,17,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8698
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8699 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 70 140 313 297 361 425 297), lower := (rows 7 19 70 140 16 32 64 128 256), losses := [] }

theorem u8699 : Upper (D 5) (R 5) [6,17,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8699
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u8699
end Delivery.IrregularNine14.P05
