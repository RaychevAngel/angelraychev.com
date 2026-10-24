import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1440 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 66, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 98 37 137 276 40 68 138 266), lower := (rows 19 98 37 137 276 40 68 128 256), losses := [] }

theorem u1440 : Upper (D 5) (R 5) [18,96,33,129,260,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1440
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1441 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 277, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 19 98 37 137 276 40 72 134 262), lower := (rows 19 98 37 137 276 40 72 128 256), losses := [] }

theorem u1441 : Upper (D 5) (R 5) [18,96,33,129,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1441
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1442 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 66, targets := 4 }], pairs := [(1,2)], upper := (rows 19 98 37 138 28 288 65 140 268), lower := (rows 19 98 37 138 28 288 65 128 256), losses := [] }

theorem u1442 : Upper (D 5) (R 5) [18,96,33,130,12,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1442
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1443 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 19 98 37 138 28 288 68 137 265), lower := (rows 19 98 37 138 28 288 68 128 256), losses := [] }

theorem u1443 : Upper (D 5) (R 5) [18,96,33,130,12,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1443
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1444 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 292, targets := 2 }], pairs := [(2,1)], upper := (rows 19 98 37 138 28 288 72 133 261), lower := (rows 19 98 37 138 28 288 72 128 256), losses := [] }

theorem u1444 : Upper (D 5) (R 5) [18,96,33,130,12,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1444
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1445 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 66, targets := 4 },{ cop := 2, region := 66, targets := 8 }], pairs := [(1,2),(1,3)], upper := (rows 19 98 37 138 276 40 65 140 268), lower := (rows 19 98 37 138 276 40 65 128 256), losses := [] }

theorem u1445 : Upper (D 5) (R 5) [18,96,33,130,260,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1445
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1446 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 66, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 98 37 138 276 40 68 137 265), lower := (rows 19 98 37 138 276 40 68 128 256), losses := [] }

theorem u1446 : Upper (D 5) (R 5) [18,96,33,130,260,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1446
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1447 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 106, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 37 138 276 40 72 133 261), lower := (rows 19 98 37 138 276 40 72 128 256), losses := [] }

theorem u1447 : Upper (D 5) (R 5) [18,96,33,130,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1447
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1448 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 66, targets := 4 },{ cop := 2, region := 66, targets := 8 }], pairs := [(1,2),(1,3)], upper := (rows 19 98 37 140 276 40 65 138 266), lower := (rows 19 98 37 140 276 40 65 128 256), losses := [] }

theorem u1448 : Upper (D 5) (R 5) [18,96,33,132,260,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1448
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1449 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 172, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 98 37 140 276 40 66 137 265), lower := (rows 19 98 37 140 276 40 66 128 256), losses := [] }

theorem u1449 : Upper (D 5) (R 5) [18,96,33,132,260,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1449
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1450 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 277, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 19 98 37 140 276 40 72 131 259), lower := (rows 19 98 37 140 276 40 72 128 256), losses := [] }

theorem u1450 : Upper (D 5) (R 5) [18,96,33,132,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1450
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1451 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 138 276 33 65 140 268), lower := (rows 19 98 44 138 276 33 65 128 256), losses := [] }

theorem u1451 : Upper (D 5) (R 5) [18,96,40,130,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1451
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1452 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 66, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 98 44 138 276 33 68 137 265), lower := (rows 19 98 44 138 276 33 68 128 256), losses := [] }

theorem u1452 : Upper (D 5) (R 5) [18,96,40,130,260,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1452
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1453 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 66, targets := 1 },{ cop := 2, region := 66, targets := 4 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 44 138 276 33 72 133 261), lower := (rows 19 98 44 138 276 33 72 128 256), losses := [] }

theorem u1453 : Upper (D 5) (R 5) [18,96,40,130,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1453
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1454 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 138 280 33 65 132 260), lower := (rows 19 98 44 138 280 33 65 128 256), losses := [] }

theorem u1454 : Upper (D 5) (R 5) [18,96,40,130,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1454
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1455 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 66, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 98 44 138 280 33 68 133 261), lower := (rows 19 98 44 138 280 33 68 128 256), losses := [] }

theorem u1455 : Upper (D 5) (R 5) [18,96,40,130,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1455
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1456 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 83, targets := 4 }], pairs := [(0,2)], upper := (rows 19 98 44 140 25 288 65 134 262), lower := (rows 19 98 44 140 25 288 65 128 256), losses := [] }

theorem u1456 : Upper (D 5) (R 5) [18,96,40,132,9,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1456
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1457 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1)], upper := (rows 19 98 44 140 25 288 66 133 261), lower := (rows 19 98 44 140 25 288 66 128 256), losses := [] }

theorem u1457 : Upper (D 5) (R 5) [18,96,40,132,9,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1457
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1458 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 19 98 44 140 25 288 68 131 259), lower := (rows 19 98 44 140 25 288 68 128 256), losses := [] }

theorem u1458 : Upper (D 5) (R 5) [18,96,40,132,9,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1458
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1459 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 140 276 33 65 138 266), lower := (rows 19 98 44 140 276 33 65 128 256), losses := [] }

theorem u1459 : Upper (D 5) (R 5) [18,96,40,132,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1459
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1460 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 140 276 33 66 137 265), lower := (rows 19 98 44 140 276 33 66 128 256), losses := [] }

theorem u1460 : Upper (D 5) (R 5) [18,96,40,132,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1460
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1461 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 66, targets := 1 },{ cop := 2, region := 66, targets := 4 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 44 140 276 33 72 131 259), lower := (rows 19 98 44 140 276 33 72 128 256), losses := [] }

theorem u1461 : Upper (D 5) (R 5) [18,96,40,132,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1461
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1462 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 140 280 33 65 134 262), lower := (rows 19 98 44 140 280 33 65 128 256), losses := [] }

theorem u1462 : Upper (D 5) (R 5) [18,96,40,132,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1462
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1463 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 44 140 280 33 66 133 261), lower := (rows 19 98 44 140 280 33 66 128 256), losses := [] }

theorem u1463 : Upper (D 5) (R 5) [18,96,40,132,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1463
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1464 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 66, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 98 44 140 280 33 68 131 259), lower := (rows 19 98 44 140 280 33 68 128 256), losses := [] }

theorem u1464 : Upper (D 5) (R 5) [18,96,40,132,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1464
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1465 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 98 133 265 28 36 66 168 296), lower := (rows 19 98 133 265 28 36 66 128 256), losses := [] }

theorem u1465 : Upper (D 5) (R 5) [18,96,129,257,12,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1465
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1466 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 164, targets := 8 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(2,3)], upper := (rows 19 98 133 265 28 36 72 162 290), lower := (rows 19 98 133 265 28 36 72 128 256), losses := [] }

theorem u1466 : Upper (D 5) (R 5) [18,96,129,257,12,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1466
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1467 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 19 98 133 265 28 36 96 138 266), lower := (rows 19 98 133 265 28 36 96 128 256), losses := [] }

theorem u1467 : Upper (D 5) (R 5) [18,96,129,257,12,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1467
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1468 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 264, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 98 133 266 28 33 68 168 296), lower := (rows 19 98 133 266 28 33 68 128 256), losses := [] }

theorem u1468 : Upper (D 5) (R 5) [18,96,129,258,12,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1468
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1469 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 164, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 98 133 266 28 33 72 164 292), lower := (rows 19 98 133 266 28 33 72 128 256), losses := [] }

theorem u1469 : Upper (D 5) (R 5) [18,96,129,258,12,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1469
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1470 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 19 98 133 266 28 33 96 140 268), lower := (rows 19 98 133 266 28 33 96 128 256), losses := [] }

theorem u1470 : Upper (D 5) (R 5) [18,96,129,258,12,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1470
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1471 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 264, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 98 133 266 28 36 65 168 296), lower := (rows 19 98 133 266 28 36 65 128 256), losses := [] }

theorem u1471 : Upper (D 5) (R 5) [18,96,129,258,12,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1471
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1472 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 164, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 98 133 266 28 36 72 161 289), lower := (rows 19 98 133 266 28 36 72 128 256), losses := [] }

theorem u1472 : Upper (D 5) (R 5) [18,96,129,258,12,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1472
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1473 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 19 98 133 266 28 36 96 137 265), lower := (rows 19 98 133 266 28 36 96 128 256), losses := [] }

theorem u1473 : Upper (D 5) (R 5) [18,96,129,258,12,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1473
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1474 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 99, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 98 133 266 28 40 65 164 292), lower := (rows 19 98 133 266 28 40 65 128 256), losses := [] }

theorem u1474 : Upper (D 5) (R 5) [18,96,129,258,12,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1474
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1475 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 296, targets := 4 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(3,2)], upper := (rows 19 98 133 266 28 40 68 161 289), lower := (rows 19 98 133 266 28 40 68 128 256), losses := [] }

theorem u1475 : Upper (D 5) (R 5) [18,96,129,258,12,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1475
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1476 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 19 98 133 266 28 40 96 133 261), lower := (rows 19 98 133 266 28 40 96 128 256), losses := [] }

theorem u1476 : Upper (D 5) (R 5) [18,96,129,258,12,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1476
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1477 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 133 296 28 33 66 140 268), lower := (rows 19 98 133 296 28 33 66 128 256), losses := [] }

theorem u1477 : Upper (D 5) (R 5) [18,96,129,288,12,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1477
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1478 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 264, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 98 133 296 28 33 68 138 266), lower := (rows 19 98 133 296 28 33 68 128 256), losses := [] }

theorem u1478 : Upper (D 5) (R 5) [18,96,129,288,12,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1478
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1479 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 133 296 28 33 72 134 262), lower := (rows 19 98 133 296 28 33 72 128 256), losses := [] }

theorem u1479 : Upper (D 5) (R 5) [18,96,129,288,12,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1479
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1480 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 264, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 98 133 296 28 36 65 138 266), lower := (rows 19 98 133 296 28 36 65 128 256), losses := [] }

theorem u1480 : Upper (D 5) (R 5) [18,96,129,288,12,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1480
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1481 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 98 133 296 28 36 66 137 265), lower := (rows 19 98 133 296 28 36 66 128 256), losses := [] }

theorem u1481 : Upper (D 5) (R 5) [18,96,129,288,12,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1481
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1482 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 133 296 28 36 72 131 259), lower := (rows 19 98 133 296 28 36 72 128 256), losses := [] }

theorem u1482 : Upper (D 5) (R 5) [18,96,129,288,12,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1482
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1483 : PairBound 9 := { available := 40, camps := [{ cop := 6, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 134 268 25 36 65 168 296), lower := (rows 19 98 134 268 25 36 65 128 256), losses := [] }

theorem u1483 : Upper (D 5) (R 5) [18,96,130,260,9,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1483
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1484 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 164, targets := 8 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(2,3)], upper := (rows 19 98 134 268 25 36 72 161 289), lower := (rows 19 98 134 268 25 36 72 128 256), losses := [] }

theorem u1484 : Upper (D 5) (R 5) [18,96,130,260,9,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1484
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1485 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 19 98 134 268 25 36 96 137 265), lower := (rows 19 98 134 268 25 36 96 128 256), losses := [] }

theorem u1485 : Upper (D 5) (R 5) [18,96,130,260,9,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1485
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1486 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 115, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 98 134 268 25 40 65 164 292), lower := (rows 19 98 134 268 25 40 65 128 256), losses := [] }

theorem u1486 : Upper (D 5) (R 5) [18,96,130,260,9,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1486
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1487 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(1,3)], upper := (rows 19 98 134 268 25 40 68 161 289), lower := (rows 19 98 134 268 25 40 68 128 256), losses := [{ target := 3, region := (rows 1 34 4 0 16 32 76 128 256), good := (rows 19 98 198 324 81 98 68 128 256) }] }

theorem u1487 : Upper (D 5) (R 5) [18,96,130,260,9,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1487
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1488 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 19 98 134 268 25 40 96 133 261), lower := (rows 19 98 134 268 25 40 96 128 256), losses := [] }

theorem u1488 : Upper (D 5) (R 5) [18,96,130,260,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1488
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1489 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 98 134 296 25 36 65 140 268), lower := (rows 19 98 134 296 25 36 65 128 256), losses := [] }

theorem u1489 : Upper (D 5) (R 5) [18,96,130,288,9,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1489
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1490 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 102, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 98 134 296 25 36 68 137 265), lower := (rows 19 98 134 296 25 36 68 128 256), losses := [] }

theorem u1490 : Upper (D 5) (R 5) [18,96,130,288,9,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1490
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1491 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 98 134 296 25 36 72 133 261), lower := (rows 19 98 134 296 25 36 72 128 256), losses := [] }

theorem u1491 : Upper (D 5) (R 5) [18,96,130,288,9,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1491
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1492 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 134 296 28 33 65 140 268), lower := (rows 19 98 134 296 28 33 65 128 256), losses := [] }

theorem u1492 : Upper (D 5) (R 5) [18,96,130,288,12,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1492
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1493 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 98 134 296 28 33 68 137 265), lower := (rows 19 98 134 296 28 33 68 128 256), losses := [] }

theorem u1493 : Upper (D 5) (R 5) [18,96,130,288,12,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1493
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1494 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 134 296 28 33 72 133 261), lower := (rows 19 98 134 296 28 33 72 128 256), losses := [] }

theorem u1494 : Upper (D 5) (R 5) [18,96,130,288,12,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1494
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1495 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 98 134 296 28 36 65 137 265), lower := (rows 19 98 134 296 28 36 65 128 256), losses := [] }

theorem u1495 : Upper (D 5) (R 5) [18,96,130,288,12,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1495
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1496 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 134 296 28 36 72 129 257), lower := (rows 19 98 134 296 28 36 72 128 256), losses := [] }

theorem u1496 : Upper (D 5) (R 5) [18,96,130,288,12,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1496
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1497 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 115, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 98 140 296 21 36 65 138 266), lower := (rows 19 98 140 296 21 36 65 128 256), losses := [] }

theorem u1497 : Upper (D 5) (R 5) [18,96,136,288,5,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1497
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1498 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 98 140 296 21 36 66 137 265), lower := (rows 19 98 140 296 21 36 66 128 256), losses := [] }

theorem u1498 : Upper (D 5) (R 5) [18,96,136,288,5,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1498
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1499 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 140 296 21 36 72 131 259), lower := (rows 19 98 140 296 21 36 72 128 256), losses := [] }

theorem u1499 : Upper (D 5) (R 5) [18,96,136,288,5,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1499
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1499
end Delivery.IrregularNine14.P05
