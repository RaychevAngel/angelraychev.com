import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0023

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3540 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 25 112 421 453 389 389), lower := (rows 35 194 13 25 112 32 64 128 256), losses := [] }

theorem u3540 : Upper (D 3) (R 3) [34,192,9,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3540
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3541 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 25 273 228 228 228 484), lower := (rows 35 194 13 25 273 32 64 128 256), losses := [] }

theorem u3541 : Upper (D 3) (R 3) [34,192,9,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3541
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3542 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 25 276 225 225 225 481), lower := (rows 35 194 13 25 276 32 64 128 256), losses := [] }

theorem u3542 : Upper (D 3) (R 3) [34,192,9,17,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3542
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3543 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 25 304 229 197 197 453), lower := (rows 35 194 13 25 304 32 64 128 256), losses := [] }

theorem u3543 : Upper (D 3) (R 3) [34,192,9,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3543
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3544 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 25 336 165 229 165 421), lower := (rows 35 194 13 25 336 32 64 128 256), losses := [] }

theorem u3544 : Upper (D 3) (R 3) [34,192,9,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3544
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3545 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 28 49 481 449 449 449), lower := (rows 35 194 13 28 49 32 64 128 256), losses := [] }

theorem u3545 : Upper (D 3) (R 3) [34,192,9,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3545
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3546 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 28 81 417 481 417 417), lower := (rows 35 194 13 28 81 32 64 128 256), losses := [] }

theorem u3546 : Upper (D 3) (R 3) [34,192,9,20,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3546
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3547 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 28 112 417 449 385 385), lower := (rows 35 194 13 28 112 32 64 128 256), losses := [] }

theorem u3547 : Upper (D 3) (R 3) [34,192,9,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3547
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3548 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 194 13 28 208 289 353 417 289), lower := (rows 35 194 13 28 208 32 64 128 256), losses := [] }

theorem u3548 : Upper (D 3) (R 3) [34,192,9,20,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3548
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3549 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 28 273 225 225 225 481), lower := (rows 35 194 13 28 273 32 64 128 256), losses := [] }

theorem u3549 : Upper (D 3) (R 3) [34,192,9,20,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3549
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3550 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 28 304 225 193 193 449), lower := (rows 35 194 13 28 304 32 64 128 256), losses := [] }

theorem u3550 : Upper (D 3) (R 3) [34,192,9,20,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3550
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3551 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 28 336 161 225 161 417), lower := (rows 35 194 13 28 336 32 64 128 256), losses := [] }

theorem u3551 : Upper (D 3) (R 3) [34,192,9,20,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3551
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3552 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 41 84 433 465 401 401), lower := (rows 35 194 13 41 84 32 64 128 256), losses := [] }

theorem u3552 : Upper (D 3) (R 3) [34,192,9,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3552
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3553 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 41 273 244 212 212 468), lower := (rows 35 194 13 41 273 32 64 128 256), losses := [] }

theorem u3553 : Upper (D 3) (R 3) [34,192,9,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3553
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3554 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 41 276 241 209 209 465), lower := (rows 35 194 13 41 276 32 64 128 256), losses := [] }

theorem u3554 : Upper (D 3) (R 3) [34,192,9,33,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3554
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3555 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 41 336 181 213 149 405), lower := (rows 35 194 13 41 336 32 64 128 256), losses := [] }

theorem u3555 : Upper (D 3) (R 3) [34,192,9,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3555
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3556 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 44 273 241 209 209 465), lower := (rows 35 194 13 44 273 32 64 128 256), losses := [] }

theorem u3556 : Upper (D 3) (R 3) [34,192,9,36,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3556
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3557 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 44 336 177 209 145 401), lower := (rows 35 194 13 44 336 32 64 128 256), losses := [] }

theorem u3557 : Upper (D 3) (R 3) [34,192,9,36,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3557
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3558 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 56 84 417 449 385 385), lower := (rows 35 194 13 56 84 32 64 128 256), losses := [] }

theorem u3558 : Upper (D 3) (R 3) [34,192,9,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3558
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3559 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 56 273 229 197 197 453), lower := (rows 35 194 13 56 273 32 64 128 256), losses := [] }

theorem u3559 : Upper (D 3) (R 3) [34,192,9,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3559
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3560 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 56 276 225 193 193 449), lower := (rows 35 194 13 56 276 32 64 128 256), losses := [] }

theorem u3560 : Upper (D 3) (R 3) [34,192,9,48,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3560
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3561 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 56 336 165 197 133 389), lower := (rows 35 194 13 56 336 32 64 128 256), losses := [] }

theorem u3561 : Upper (D 3) (R 3) [34,192,9,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3561
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3562 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 73 52 433 465 401 401), lower := (rows 35 194 13 73 52 32 64 128 256), losses := [] }

theorem u3562 : Upper (D 3) (R 3) [34,192,9,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3562
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3563 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 73 148 305 369 433 305), lower := (rows 35 194 13 73 148 32 64 128 256), losses := [] }

theorem u3563 : Upper (D 3) (R 3) [34,192,9,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3563
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3564 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 73 176 309 341 405 277), lower := (rows 35 194 13 73 176 32 64 128 256), losses := [] }

theorem u3564 : Upper (D 3) (R 3) [34,192,9,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3564
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3565 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 73 273 180 244 180 436), lower := (rows 35 194 13 73 273 32 64 128 256), losses := [] }

theorem u3565 : Upper (D 3) (R 3) [34,192,9,65,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3565
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3566 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 73 276 177 241 177 433), lower := (rows 35 194 13 73 276 32 64 128 256), losses := [] }

theorem u3566 : Upper (D 3) (R 3) [34,192,9,65,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3566
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3567 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 73 304 181 213 149 405), lower := (rows 35 194 13 73 304 32 64 128 256), losses := [] }

theorem u3567 : Upper (D 3) (R 3) [34,192,9,65,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3567
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3568 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 73 400 53 117 181 309), lower := (rows 35 194 13 73 400 32 64 128 256), losses := [] }

theorem u3568 : Upper (D 3) (R 3) [34,192,9,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3568
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3569 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 76 176 305 337 401 273), lower := (rows 35 194 13 76 176 32 64 128 256), losses := [] }

theorem u3569 : Upper (D 3) (R 3) [34,192,9,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3569
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3570 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 76 273 177 241 177 433), lower := (rows 35 194 13 76 273 32 64 128 256), losses := [] }

theorem u3570 : Upper (D 3) (R 3) [34,192,9,68,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3570
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3571 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 76 304 177 209 145 401), lower := (rows 35 194 13 76 304 32 64 128 256), losses := [] }

theorem u3571 : Upper (D 3) (R 3) [34,192,9,68,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3571
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3572 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 76 400 49 113 177 305), lower := (rows 35 194 13 76 400 32 64 128 256), losses := [] }

theorem u3572 : Upper (D 3) (R 3) [34,192,9,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3572
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3573 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 88 52 417 449 385 385), lower := (rows 35 194 13 88 52 32 64 128 256), losses := [] }

theorem u3573 : Upper (D 3) (R 3) [34,192,9,80,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3573
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3574 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 88 148 289 353 417 289), lower := (rows 35 194 13 88 148 32 64 128 256), losses := [] }

theorem u3574 : Upper (D 3) (R 3) [34,192,9,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3574
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3575 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 88 176 293 325 389 261), lower := (rows 35 194 13 88 176 32 64 128 256), losses := [] }

theorem u3575 : Upper (D 3) (R 3) [34,192,9,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3575
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3576 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 88 273 165 229 165 421), lower := (rows 35 194 13 88 273 32 64 128 256), losses := [] }

theorem u3576 : Upper (D 3) (R 3) [34,192,9,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3576
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3577 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 88 276 161 225 161 417), lower := (rows 35 194 13 88 276 32 64 128 256), losses := [] }

theorem u3577 : Upper (D 3) (R 3) [34,192,9,80,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3577
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3578 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 88 304 165 197 133 389), lower := (rows 35 194 13 88 304 32 64 128 256), losses := [] }

theorem u3578 : Upper (D 3) (R 3) [34,192,9,80,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3578
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3579 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 88 400 37 101 165 293), lower := (rows 35 194 13 88 400 32 64 128 256), losses := [] }

theorem u3579 : Upper (D 3) (R 3) [34,192,9,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3579
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3580 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 104 148 305 337 401 273), lower := (rows 35 194 13 104 148 32 64 128 256), losses := [] }

theorem u3580 : Upper (D 3) (R 3) [34,192,9,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3580
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3581 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 104 273 181 213 149 405), lower := (rows 35 194 13 104 273 32 64 128 256), losses := [] }

theorem u3581 : Upper (D 3) (R 3) [34,192,9,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3581
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3582 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 104 276 177 209 145 401), lower := (rows 35 194 13 104 276 32 64 128 256), losses := [] }

theorem u3582 : Upper (D 3) (R 3) [34,192,9,96,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3582
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3583 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 104 400 53 85 149 277), lower := (rows 35 194 13 104 400 32 64 128 256), losses := [] }

theorem u3583 : Upper (D 3) (R 3) [34,192,9,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3583
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3584 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 13 200 52 305 337 401 273), lower := (rows 35 194 13 200 52 32 64 128 256), losses := [] }

theorem u3584 : Upper (D 3) (R 3) [34,192,9,192,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3584
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3585 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 13 200 273 53 117 181 309), lower := (rows 35 194 13 200 273 32 64 128 256), losses := [] }

theorem u3585 : Upper (D 3) (R 3) [34,192,9,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3585
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3586 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 13 200 276 49 113 177 305), lower := (rows 35 194 13 200 276 32 64 128 256), losses := [] }

theorem u3586 : Upper (D 3) (R 3) [34,192,9,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3586
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3587 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 13 200 304 53 85 149 277), lower := (rows 35 194 13 200 304 32 64 128 256), losses := [] }

theorem u3587 : Upper (D 3) (R 3) [34,192,9,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3587
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3588 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 265 52 241 209 209 465), lower := (rows 35 194 13 265 52 32 64 128 256), losses := [] }

theorem u3588 : Upper (D 3) (R 3) [34,192,9,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3588
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3589 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 265 84 177 241 177 433), lower := (rows 35 194 13 265 84 32 64 128 256), losses := [] }

theorem u3589 : Upper (D 3) (R 3) [34,192,9,257,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3589
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3590 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 265 112 181 213 149 405), lower := (rows 35 194 13 265 112 32 64 128 256), losses := [] }

theorem u3590 : Upper (D 3) (R 3) [34,192,9,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3590
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3591 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 268 49 241 209 209 465), lower := (rows 35 194 13 268 49 32 64 128 256), losses := [] }

theorem u3591 : Upper (D 3) (R 3) [34,192,9,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3591
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3592 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 268 81 177 241 177 433), lower := (rows 35 194 13 268 81 32 64 128 256), losses := [] }

theorem u3592 : Upper (D 3) (R 3) [34,192,9,260,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3592
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3593 : Route 9 := (fun mask => (mask,id))

def c3593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3593 : Upper (D 3) (R 3) [34,192,9,260,96] 13 := by
  apply FastRouting.sound _ _ [34,192,9,260,96] 13 (by decide) (choices 1) [1,16,128] r3593 c3593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1401
  · exact u1402
  · exact u1403

def b3594 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 194 13 268 208 49 113 177 305), lower := (rows 35 194 13 268 208 32 64 128 256), losses := [] }

theorem u3594 : Upper (D 3) (R 3) [34,192,9,260,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3594
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3595 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 280 49 229 197 197 453), lower := (rows 35 194 13 280 49 32 64 128 256), losses := [] }

theorem u3595 : Upper (D 3) (R 3) [34,192,9,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3595
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3596 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 280 52 225 193 193 449), lower := (rows 35 194 13 280 52 32 64 128 256), losses := [] }

theorem u3596 : Upper (D 3) (R 3) [34,192,9,272,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3596
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3597 : PairBound 9 := { available := 165, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 280 81 165 229 165 421), lower := (rows 35 194 13 280 81 32 64 128 256), losses := [] }

theorem u3597 : Upper (D 3) (R 3) [34,192,9,272,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3597
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3598 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 280 84 161 225 161 417), lower := (rows 35 194 13 280 84 32 64 128 256), losses := [] }

theorem u3598 : Upper (D 3) (R 3) [34,192,9,272,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3598
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3599 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 280 112 165 197 133 389), lower := (rows 35 194 13 280 112 32 64 128 256), losses := [] }

theorem u3599 : Upper (D 3) (R 3) [34,192,9,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3599
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u3599
end Delivery.IrregularNine14.P03
