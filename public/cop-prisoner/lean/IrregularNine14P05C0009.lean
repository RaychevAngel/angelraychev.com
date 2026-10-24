import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b540 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 42 84 140 280 33 66 161 289), lower := (rows 7 42 84 140 280 33 66 128 256), losses := [] }

theorem u540 : Upper (D 5) (R 5) [6,40,80,132,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b540
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b541 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 84 140 280 33 96 131 259), lower := (rows 7 42 84 140 280 33 96 128 256), losses := [] }

theorem u541 : Upper (D 5) (R 5) [6,40,80,132,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b541
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b542 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 84 140 304 33 65 138 266), lower := (rows 7 42 84 140 304 33 65 128 256), losses := [] }

theorem u542 : Upper (D 5) (R 5) [6,40,80,132,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b542
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b543 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 42 84 140 304 33 66 137 265), lower := (rows 7 42 84 140 304 33 66 128 256), losses := [] }

theorem u543 : Upper (D 5) (R 5) [6,40,80,132,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b543
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b544 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 304, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 84 140 304 33 72 131 259), lower := (rows 7 42 84 140 304 33 72 128 256), losses := [] }

theorem u544 : Upper (D 5) (R 5) [6,40,80,132,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b544
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b545 : PairBound 9 := { available := 40, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 42 196 26 276 33 65 168 296), lower := (rows 7 42 196 26 276 33 65 128 256), losses := [{ target := 0, region := (rows 0 34 4 41 17 32 64 162 290), good := (rows 414 426 196 410 276 442 88 128 256) }] }

theorem u545 : Upper (D 5) (R 5) [6,40,192,18,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b545
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b546 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 196 26 276 33 72 161 289), lower := (rows 7 42 196 26 276 33 72 128 256), losses := [] }

theorem u546 : Upper (D 5) (R 5) [6,40,192,18,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b546
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b547 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 196 26 276 33 96 137 265), lower := (rows 7 42 196 26 276 33 96 128 256), losses := [] }

theorem u547 : Upper (D 5) (R 5) [6,40,192,18,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b547
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b548 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 28 274 33 65 168 296), lower := (rows 7 42 196 28 274 33 65 128 256), losses := [] }

theorem u548 : Upper (D 5) (R 5) [6,40,192,20,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b548
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b549 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 196 28 274 33 72 161 289), lower := (rows 7 42 196 28 274 33 72 128 256), losses := [] }

theorem u549 : Upper (D 5) (R 5) [6,40,192,20,258,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b549
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b550 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 196 28 274 33 96 137 265), lower := (rows 7 42 196 28 274 33 96 128 256), losses := [] }

theorem u550 : Upper (D 5) (R 5) [6,40,192,20,258,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b550
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b551 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 42 196 268 25 33 66 176 304), lower := (rows 7 42 196 268 25 33 66 128 256), losses := [] }

theorem u551 : Upper (D 5) (R 5) [6,40,192,260,9,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b551
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b552 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2)], upper := (rows 7 42 196 268 25 33 80 162 290), lower := (rows 7 42 196 268 25 33 80 128 256), losses := [] }

theorem u552 : Upper (D 5) (R 5) [6,40,192,260,9,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b552
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b553 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 196 268 25 33 96 146 274), lower := (rows 7 42 196 268 25 33 96 128 256), losses := [] }

theorem u553 : Upper (D 5) (R 5) [6,40,192,260,9,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b553
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b554 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 50 69 41 152 288 66 140 268), lower := (rows 7 50 69 41 152 288 66 128 256), losses := [] }

theorem u554 : Upper (D 5) (R 5) [6,48,65,33,136,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b554
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b555 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 50 69 41 152 288 68 138 266), lower := (rows 7 50 69 41 152 288 68 128 256), losses := [] }

theorem u555 : Upper (D 5) (R 5) [6,48,65,33,136,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b555
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b556 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 68, targets := 2 }], pairs := [(2,1)], upper := (rows 7 50 69 41 152 288 72 134 262), lower := (rows 7 50 69 41 152 288 72 128 256), losses := [] }

theorem u556 : Upper (D 5) (R 5) [6,48,65,33,136,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b556
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b557 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 50 69 44 152 288 65 138 266), lower := (rows 7 50 69 44 152 288 65 128 256), losses := [] }

theorem u557 : Upper (D 5) (R 5) [6,48,65,36,136,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b557
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b558 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 50 69 44 152 288 66 137 265), lower := (rows 7 50 69 44 152 288 66 128 256), losses := [] }

theorem u558 : Upper (D 5) (R 5) [6,48,65,36,136,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b558
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b559 : PairBound 9 := { available := 3, camps := [], pairs := [(1,2)], upper := (rows 7 50 69 44 152 288 72 131 259), lower := (rows 7 50 69 44 152 288 72 128 256), losses := [{ target := 2, region := (rows 1 90 0 8 24 301 88 133 261), good := (rows 419 114 483 506 250 288 122 128 288) }] }

theorem u559 : Upper (D 5) (R 5) [6,48,65,36,136,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b559
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b560 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 138 280 33 68 168 296), lower := (rows 7 50 69 138 280 33 68 128 256), losses := [] }

theorem u560 : Upper (D 5) (R 5) [6,48,65,130,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b560
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b561 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 138 280 33 72 164 292), lower := (rows 7 50 69 138 280 33 72 128 256), losses := [] }

theorem u561 : Upper (D 5) (R 5) [6,48,65,130,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b561
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b562 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 103, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 50 69 138 280 33 96 140 268), lower := (rows 7 50 69 138 280 33 96 128 256), losses := [] }

theorem u562 : Upper (D 5) (R 5) [6,48,65,130,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b562
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b563 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 138 280 36 65 168 296), lower := (rows 7 50 69 138 280 36 65 128 256), losses := [] }

theorem u563 : Upper (D 5) (R 5) [6,48,65,130,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b563
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b564 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 138 280 36 72 161 289), lower := (rows 7 50 69 138 280 36 72 128 256), losses := [] }

theorem u564 : Upper (D 5) (R 5) [6,48,65,130,264,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b564
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b565 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 50 69 138 280 36 96 137 265), lower := (rows 7 50 69 138 280 36 96 128 256), losses := [] }

theorem u565 : Upper (D 5) (R 5) [6,48,65,130,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b565
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b566 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 103, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 50 69 168 280 33 66 140 268), lower := (rows 7 50 69 168 280 33 66 128 256), losses := [] }

theorem u566 : Upper (D 5) (R 5) [6,48,65,160,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b566
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b567 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 168 280 33 68 138 266), lower := (rows 7 50 69 168 280 33 68 128 256), losses := [] }

theorem u567 : Upper (D 5) (R 5) [6,48,65,160,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b567
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b568 : PairBound 9 := { available := 6, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 50 69 168 280 33 72 134 262), lower := (rows 7 50 69 168 280 33 72 128 256), losses := [{ target := 0, region := (rows 0 42 4 40 48 32 122 129 257), good := (rows 454 122 452 250 346 506 74 128 256) }] }

theorem u568 : Upper (D 5) (R 5) [6,48,65,160,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b568
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b569 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 168 280 36 65 138 266), lower := (rows 7 50 69 168 280 36 65 128 256), losses := [] }

theorem u569 : Upper (D 5) (R 5) [6,48,65,160,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b569
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b570 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 103, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 50 69 168 280 36 66 137 265), lower := (rows 7 50 69 168 280 36 66 128 256), losses := [] }

theorem u570 : Upper (D 5) (R 5) [6,48,65,160,264,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b570
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b571 : PairBound 9 := { available := 3, camps := [], pairs := [(0,5),(2,5)], upper := (rows 7 50 69 168 280 36 72 131 259), lower := (rows 7 50 69 168 280 36 72 128 256), losses := [{ target := 5, region := (rows 3 2 6 8 16 0 88 131 259), good := (rows 391 471 453 200 344 4 72 128 256) }] }

theorem u571 : Upper (D 5) (R 5) [6,48,65,160,264,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b571
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b572 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(3,1)], upper := (rows 7 50 76 41 145 288 66 140 268), lower := (rows 7 50 76 41 145 288 66 128 256), losses := [] }

theorem u572 : Upper (D 5) (R 5) [6,48,72,33,129,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b572
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b573 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 50 76 41 145 288 68 138 266), lower := (rows 7 50 76 41 145 288 68 128 256), losses := [] }

theorem u573 : Upper (D 5) (R 5) [6,48,72,33,129,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b573
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b574 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 435, targets := 8 }], pairs := [(0,3)], upper := (rows 7 50 76 41 145 288 72 134 262), lower := (rows 7 50 76 41 145 288 72 128 256), losses := [] }

theorem u574 : Upper (D 5) (R 5) [6,48,72,33,129,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b574
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b575 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 296, targets := 1 }], pairs := [(3,0)], upper := (rows 7 50 76 44 145 288 65 138 266), lower := (rows 7 50 76 44 145 288 65 128 256), losses := [] }

theorem u575 : Upper (D 5) (R 5) [6,48,72,36,129,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b575
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b576 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(3,1)], upper := (rows 7 50 76 44 145 288 66 137 265), lower := (rows 7 50 76 44 145 288 66 128 256), losses := [] }

theorem u576 : Upper (D 5) (R 5) [6,48,72,36,129,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b576
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b577 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 434, targets := 4 }], pairs := [(1,2)], upper := (rows 7 50 76 44 145 288 72 131 259), lower := (rows 7 50 76 44 145 288 72 128 256), losses := [] }

theorem u577 : Upper (D 5) (R 5) [6,48,72,36,129,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b577
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b578 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 402, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 44 152 33 65 386 258), lower := (rows 7 50 76 44 152 33 65 128 256), losses := [] }

theorem u578 : Upper (D 5) (R 5) [6,48,72,36,136,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b578
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b579 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 76 44 152 33 66 385 257), lower := (rows 7 50 76 44 152 33 66 128 256), losses := [] }

theorem u579 : Upper (D 5) (R 5) [6,48,72,36,136,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b579
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b580 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 7 50 76 44 152 33 320 131 259), lower := (rows 7 50 76 44 152 33 320 128 256), losses := [] }

theorem u580 : Upper (D 5) (R 5) [6,48,72,36,136,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b580
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b581 : PairBound 9 := { available := 3, camps := [], pairs := [(1,2)], upper := (rows 7 50 76 44 152 288 65 131 259), lower := (rows 7 50 76 44 152 288 65 128 256), losses := [{ target := 2, region := (rows 1 15 0 8 20 357 65 193 321), good := (rows 499 50 506 58 154 288 483 128 288) }] }

theorem u581 : Upper (D 5) (R 5) [6,48,72,36,136,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b581
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b582 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(3,1)], upper := (rows 7 50 76 44 152 288 66 129 257), lower := (rows 7 50 76 44 152 288 66 128 256), losses := [] }

theorem u582 : Upper (D 5) (R 5) [6,48,72,36,136,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b582
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b583 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 402, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 44 400 33 65 138 266), lower := (rows 7 50 76 44 400 33 65 128 256), losses := [] }

theorem u583 : Upper (D 5) (R 5) [6,48,72,36,384,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b583
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b584 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 76 44 400 33 66 137 265), lower := (rows 7 50 76 44 400 33 66 128 256), losses := [] }

theorem u584 : Upper (D 5) (R 5) [6,48,72,36,384,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b584
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b585 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 434, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 50 76 44 400 33 72 131 259), lower := (rows 7 50 76 44 400 33 72 128 256), losses := [] }

theorem u585 : Upper (D 5) (R 5) [6,48,72,36,384,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b585
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b586 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 76 137 273 40 66 164 292), lower := (rows 7 50 76 137 273 40 66 128 256), losses := [] }

theorem u586 : Upper (D 5) (R 5) [6,48,72,129,257,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b586
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b587 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 50 76 137 273 40 68 162 290), lower := (rows 7 50 76 137 273 40 68 128 256), losses := [] }

theorem u587 : Upper (D 5) (R 5) [6,48,72,129,257,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b587
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b588 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 50 76 137 273 40 96 134 262), lower := (rows 7 50 76 137 273 40 96 128 256), losses := [] }

theorem u588 : Upper (D 5) (R 5) [6,48,72,129,257,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b588
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b589 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 306, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 7 50 76 137 280 36 65 162 290), lower := (rows 7 50 76 137 280 36 65 128 256), losses := [] }

theorem u589 : Upper (D 5) (R 5) [6,48,72,129,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b589
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b590 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 76 137 280 36 66 161 289), lower := (rows 7 50 76 137 280 36 66 128 256), losses := [] }

theorem u590 : Upper (D 5) (R 5) [6,48,72,129,264,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b590
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b591 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 50 76 137 280 36 96 131 259), lower := (rows 7 50 76 137 280 36 96 128 256), losses := [] }

theorem u591 : Upper (D 5) (R 5) [6,48,72,129,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b591
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b592 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 138 273 40 65 164 292), lower := (rows 7 50 76 138 273 40 65 128 256), losses := [] }

theorem u592 : Upper (D 5) (R 5) [6,48,72,130,257,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b592
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b593 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 50 76 138 273 40 68 161 289), lower := (rows 7 50 76 138 273 40 68 128 256), losses := [] }

theorem u593 : Upper (D 5) (R 5) [6,48,72,130,257,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b593
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b594 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 272, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 50 76 138 273 40 96 133 261), lower := (rows 7 50 76 138 273 40 96 128 256), losses := [] }

theorem u594 : Upper (D 5) (R 5) [6,48,72,130,257,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b594
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b595 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 138 280 33 65 164 292), lower := (rows 7 50 76 138 280 33 65 128 256), losses := [] }

theorem u595 : Upper (D 5) (R 5) [6,48,72,130,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b595
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b596 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 50 76 138 280 33 68 161 289), lower := (rows 7 50 76 138 280 33 68 128 256), losses := [] }

theorem u596 : Upper (D 5) (R 5) [6,48,72,130,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b596
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b597 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 50 76 138 280 33 96 133 261), lower := (rows 7 50 76 138 280 33 96 128 256), losses := [] }

theorem u597 : Upper (D 5) (R 5) [6,48,72,130,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b597
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b598 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 50 76 138 280 36 65 161 289), lower := (rows 7 50 76 138 280 36 65 128 256), losses := [] }

theorem u598 : Upper (D 5) (R 5) [6,48,72,130,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b598
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b599 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 50 76 138 280 36 96 129 257), lower := (rows 7 50 76 138 280 36 96 128 256), losses := [] }

theorem u599 : Upper (D 5) (R 5) [6,48,72,130,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b599
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u599
end Delivery.IrregularNine14.P05
