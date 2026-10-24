import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1440 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 44 137 144 96 86 150 278), lower := (rows 275 98 44 137 144 96 64 128 256), losses := [] }

theorem u1440 : Upper (D 1) (R 1) [274,96,40,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1440
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1441 : PairBound 9 := { available := 84, camps := [], pairs := [], upper := (rows 275 98 44 138 144 33 84 212 340), lower := (rows 275 98 44 138 144 33 64 128 256), losses := [] }

theorem u1441 : Upper (D 1) (R 1) [274,96,40,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1441
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1442 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 275 98 44 138 144 36 81 209 337), lower := (rows 275 98 44 138 144 36 64 128 256), losses := [] }

theorem u1442 : Upper (D 1) (R 1) [274,96,40,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1442
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1443 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 52, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 44 138 144 48 69 197 325), lower := (rows 275 98 44 138 144 48 64 128 256), losses := [] }

theorem u1443 : Upper (D 1) (R 1) [274,96,40,130,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1443
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1444 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 44 138 144 96 85 149 277), lower := (rows 275 98 44 138 144 96 64 128 256), losses := [] }

theorem u1444 : Upper (D 1) (R 1) [274,96,40,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1444
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1445 : PairBound 9 := { available := 22, camps := [], pairs := [], upper := (rows 275 98 44 200 144 33 86 150 278), lower := (rows 275 98 44 200 144 33 64 128 256), losses := [] }

theorem u1445 : Upper (D 1) (R 1) [274,96,40,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1445
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1446 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 44 200 144 34 85 149 277), lower := (rows 275 98 44 200 144 34 64 128 256), losses := [] }

theorem u1446 : Upper (D 1) (R 1) [274,96,40,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1446
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1447 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 275 98 44 200 144 36 83 147 275), lower := (rows 275 98 44 200 144 36 64 128 256), losses := [] }

theorem u1447 : Upper (D 1) (R 1) [274,96,40,192,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1447
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1448 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 52, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 44 200 144 48 71 135 263), lower := (rows 275 98 44 200 144 48 64 128 256), losses := [] }

theorem u1448 : Upper (D 1) (R 1) [274,96,40,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1448
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1449 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 52 137 144 34 76 204 332), lower := (rows 275 98 52 137 144 34 64 128 256), losses := [] }

theorem u1449 : Upper (D 1) (R 1) [274,96,48,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1449
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1450 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 275 98 52 137 144 36 74 202 330), lower := (rows 275 98 52 137 144 36 64 128 256), losses := [] }

theorem u1450 : Upper (D 1) (R 1) [274,96,48,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1450
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1451 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 275 98 52 137 144 40 70 198 326), lower := (rows 275 98 52 137 144 40 64 128 256), losses := [] }

theorem u1451 : Upper (D 1) (R 1) [274,96,48,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1451
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1452 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 52 137 144 96 78 142 270), lower := (rows 275 98 52 137 144 96 64 128 256), losses := [] }

theorem u1452 : Upper (D 1) (R 1) [274,96,48,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1452
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1453 : PairBound 9 := { available := 76, camps := [], pairs := [], upper := (rows 275 98 52 138 144 33 76 204 332), lower := (rows 275 98 52 138 144 33 64 128 256), losses := [] }

theorem u1453 : Upper (D 1) (R 1) [274,96,48,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1453
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1454 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 275 98 52 138 144 36 73 201 329), lower := (rows 275 98 52 138 144 36 64 128 256), losses := [] }

theorem u1454 : Upper (D 1) (R 1) [274,96,48,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1454
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1455 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 275 98 52 138 144 40 69 197 325), lower := (rows 275 98 52 138 144 40 64 128 256), losses := [] }

theorem u1455 : Upper (D 1) (R 1) [274,96,48,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1455
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1456 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 52 138 144 96 77 141 269), lower := (rows 275 98 52 138 144 96 64 128 256), losses := [] }

theorem u1456 : Upper (D 1) (R 1) [274,96,48,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1456
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1457 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 275 98 52 140 144 33 74 202 330), lower := (rows 275 98 52 140 144 33 64 128 256), losses := [] }

theorem u1457 : Upper (D 1) (R 1) [274,96,48,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1457
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1458 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 52 140 144 34 73 201 329), lower := (rows 275 98 52 140 144 34 64 128 256), losses := [] }

theorem u1458 : Upper (D 1) (R 1) [274,96,48,132,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1458
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1459 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 275 98 52 140 144 40 67 195 323), lower := (rows 275 98 52 140 144 40 64 128 256), losses := [] }

theorem u1459 : Upper (D 1) (R 1) [274,96,48,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1459
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1460 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 52 140 144 96 75 139 267), lower := (rows 275 98 52 140 144 96 64 128 256), losses := [] }

theorem u1460 : Upper (D 1) (R 1) [274,96,48,132,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1460
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1461 : PairBound 9 := { available := 14, camps := [], pairs := [], upper := (rows 275 98 52 200 144 33 78 142 270), lower := (rows 275 98 52 200 144 33 64 128 256), losses := [] }

theorem u1461 : Upper (D 1) (R 1) [274,96,48,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1461
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1462 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 52 200 144 34 77 141 269), lower := (rows 275 98 52 200 144 34 64 128 256), losses := [] }

theorem u1462 : Upper (D 1) (R 1) [274,96,48,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1462
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1463 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 275 98 52 200 144 36 75 139 267), lower := (rows 275 98 52 200 144 36 64 128 256), losses := [] }

theorem u1463 : Upper (D 1) (R 1) [274,96,48,192,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1463
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1464 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 275 98 52 200 144 40 71 135 263), lower := (rows 275 98 52 200 144 40 64 128 256), losses := [] }

theorem u1464 : Upper (D 1) (R 1) [274,96,48,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1464
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1465 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 277 11 38 200 80 34 240 176 432), lower := (rows 277 11 38 200 80 34 64 128 256), losses := [] }

theorem u1465 : Upper (D 1) (R 1) [276,9,34,192,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1465
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1466 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 277 11 38 200 80 48 226 162 418), lower := (rows 277 11 38 200 80 48 64 128 256), losses := [] }

theorem u1466 : Upper (D 1) (R 1) [276,9,34,192,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1466
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1467 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 277 11 38 200 80 160 114 178 306), lower := (rows 277 11 38 200 80 160 64 128 256), losses := [] }

theorem u1467 : Upper (D 1) (R 1) [276,9,34,192,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1467
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1468 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 42, targets := 16 }], pairs := [(1,4)], upper := (rows 277 11 100 42 144 34 208 208 464), lower := (rows 277 11 100 42 144 34 64 128 256), losses := [] }

theorem u1468 : Upper (D 1) (R 1) [276,9,96,34,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1468
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1469 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 42, targets := 64 }], pairs := [(1,6)], upper := (rows 277 11 100 42 144 48 194 194 450), lower := (rows 277 11 100 42 144 48 64 128 256), losses := [] }

theorem u1469 : Upper (D 1) (R 1) [276,9,96,34,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1469
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1470 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 277 11 100 42 144 96 210 146 402), lower := (rows 277 11 100 42 144 96 64 128 256), losses := [] }

theorem u1470 : Upper (D 1) (R 1) [276,9,96,34,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1470
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1471 : PairBound 9 := { available := 82, camps := [], pairs := [(1,4)], upper := (rows 277 11 100 42 144 160 82 210 338), lower := (rows 277 11 100 42 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 9 0 176 64 128 256), good := (rows 303 11 100 42 160 160 64 160 256) }] }

theorem u1471 : Upper (D 1) (R 1) [276,9,96,34,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1471
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1472 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 469, targets := 2 }], pairs := [(0,1)], upper := (rows 277 11 100 138 144 34 112 240 368), lower := (rows 277 11 100 138 144 34 64 128 256), losses := [] }

theorem u1472 : Upper (D 1) (R 1) [276,9,96,130,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1472
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1473 : PairBound 9 := { available := 98, camps := [], pairs := [(2,7)], upper := (rows 277 11 100 138 144 48 98 226 354), lower := (rows 277 11 100 138 144 48 64 128 256), losses := [{ target := 7, region := (rows 1 2 6 8 16 49 66 0 258), good := (rows 309 367 100 334 48 48 64 0 256) }] }

theorem u1473 : Upper (D 1) (R 1) [276,9,96,130,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1473
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1474 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 277 11 100 138 144 96 114 178 306), lower := (rows 277 11 100 138 144 96 64 128 256), losses := [] }

theorem u1474 : Upper (D 1) (R 1) [276,9,96,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1474
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1475 : PairBound 9 := { available := 208, camps := [], pairs := [(0,5)], upper := (rows 277 11 100 168 18 34 208 208 464), lower := (rows 277 11 100 168 18 34 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 8 50 0 127 191 319), good := (rows 469 475 469 472 466 466 64 128 256) }] }

theorem u1475 : Upper (D 1) (R 1) [276,9,96,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1475
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1476 : PairBound 9 := { available := 194, camps := [], pairs := [(2,4)], upper := (rows 277 11 100 168 18 48 194 194 450), lower := (rows 277 11 100 168 18 48 64 128 256), losses := [{ target := 4, region := (rows 1 2 36 40 0 32 82 146 274), good := (rows 453 459 108 172 450 492 64 128 256) }] }

theorem u1476 : Upper (D 1) (R 1) [276,9,96,160,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1476
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1477 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 277 11 100 168 18 96 210 146 402), lower := (rows 277 11 100 168 18 96 64 128 256), losses := [] }

theorem u1477 : Upper (D 1) (R 1) [276,9,96,160,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1477
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1478 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 277 11 100 168 18 160 82 210 338), lower := (rows 277 11 100 168 18 160 64 128 256), losses := [] }

theorem u1478 : Upper (D 1) (R 1) [276,9,96,160,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1478
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1479 : PairBound 9 := { available := 82, camps := [], pairs := [(0,5)], upper := (rows 277 11 100 168 144 34 82 210 338), lower := (rows 277 11 100 168 144 34 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 8 190 0 98 162 290), good := (rows 277 475 469 472 144 466 64 144 256) }] }

theorem u1479 : Upper (D 1) (R 1) [276,9,96,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1479
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1480 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 277 11 100 168 144 48 66 194 322), lower := (rows 277 11 100 168 144 48 64 128 256), losses := [] }

theorem u1480 : Upper (D 1) (R 1) [276,9,96,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1480
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1481 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 277 11 100 168 144 96 82 146 274), lower := (rows 277 11 100 168 144 96 64 128 256), losses := [] }

theorem u1481 : Upper (D 1) (R 1) [276,9,96,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1481
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1482 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 26 100 42 144 33 194 194 450), lower := (rows 277 26 100 42 144 33 64 128 256), losses := [] }

theorem u1482 : Upper (D 1) (R 1) [276,24,96,34,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1482
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1483 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 42, targets := 64 }], pairs := [(1,6)], upper := (rows 277 26 100 42 144 34 193 193 449), lower := (rows 277 26 100 42 144 34 64 128 256), losses := [] }

theorem u1483 : Upper (D 1) (R 1) [276,24,96,34,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1483
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1484 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 277 26 100 42 144 96 195 131 387), lower := (rows 277 26 100 42 144 96 64 128 256), losses := [] }

theorem u1484 : Upper (D 1) (R 1) [276,24,96,34,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1484
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1485 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 42, targets := 64 }], pairs := [(1,6)], upper := (rows 277 26 100 42 144 160 67 195 323), lower := (rows 277 26 100 42 144 160 64 128 256), losses := [] }

theorem u1485 : Upper (D 1) (R 1) [276,24,96,34,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1485
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1486 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 277 35 14 200 48 34 208 208 464), lower := (rows 277 35 14 200 48 34 64 128 256), losses := [] }

theorem u1486 : Upper (D 1) (R 1) [276,33,10,192,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1486
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1487 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 204, targets := 16 }], pairs := [(2,4)], upper := (rows 277 35 14 200 48 48 194 194 450), lower := (rows 277 35 14 200 48 48 64 128 256), losses := [] }

theorem u1487 : Upper (D 1) (R 1) [276,33,10,192,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1487
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1488 : PairBound 9 := { available := 146, camps := [], pairs := [(0,6)], upper := (rows 277 35 14 200 48 96 210 146 402), lower := (rows 277 35 14 200 48 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 50 32 0 134 262), good := (rows 405 435 415 136 48 48 0 128 256) }] }

theorem u1488 : Upper (D 1) (R 1) [276,33,10,192,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1488
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1489 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 70 56 144 34 200 200 456), lower := (rows 277 35 70 56 144 34 64 128 256), losses := [] }

theorem u1489 : Upper (D 1) (R 1) [276,33,66,48,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1489
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1490 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 35 70 56 144 40 194 194 450), lower := (rows 277 35 70 56 144 40 64 128 256), losses := [] }

theorem u1490 : Upper (D 1) (R 1) [276,33,66,48,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1490
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1491 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 277 35 70 56 144 96 202 138 394), lower := (rows 277 35 70 56 144 96 64 128 256), losses := [] }

theorem u1491 : Upper (D 1) (R 1) [276,33,66,48,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1491
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1492 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 277 35 70 56 144 160 74 202 330), lower := (rows 277 35 70 56 144 160 64 128 256), losses := [] }

theorem u1492 : Upper (D 1) (R 1) [276,33,66,48,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1492
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1493 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 35 70 88 144 34 232 168 424), lower := (rows 277 35 70 88 144 34 64 128 256), losses := [] }

theorem u1493 : Upper (D 1) (R 1) [276,33,66,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1493
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1494 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 277 35 70 88 144 40 226 162 418), lower := (rows 277 35 70 88 144 40 64 128 256), losses := [] }

theorem u1494 : Upper (D 1) (R 1) [276,33,66,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1494
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1495 : PairBound 9 := { available := 42, camps := [], pairs := [(1,4)], upper := (rows 277 35 70 88 144 160 106 170 298), lower := (rows 277 35 70 88 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 176 64 128 256), good := (rows 295 35 70 104 160 160 64 160 256) }] }

theorem u1495 : Upper (D 1) (R 1) [276,33,66,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1495
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1496 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 35 70 104 144 34 216 152 408), lower := (rows 277 35 70 104 144 34 64 128 256), losses := [] }

theorem u1496 : Upper (D 1) (R 1) [276,33,66,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1496
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1497 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 35 70 104 144 40 210 146 402), lower := (rows 277 35 70 104 144 40 64 128 256), losses := [] }

theorem u1497 : Upper (D 1) (R 1) [276,33,66,96,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1497
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1498 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 70 104 144 48 202 138 394), lower := (rows 277 35 70 104 144 48 64 128 256), losses := [] }

theorem u1498 : Upper (D 1) (R 1) [276,33,66,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1498
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1499 : PairBound 9 := { available := 26, camps := [], pairs := [(1,4)], upper := (rows 277 35 70 104 144 160 90 154 282), lower := (rows 277 35 70 104 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 176 64 128 256), good := (rows 295 35 70 104 160 160 64 160 256) }] }

theorem u1499 : Upper (D 1) (R 1) [276,33,66,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1499
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1499
end Delivery.IrregularNine14.P01
