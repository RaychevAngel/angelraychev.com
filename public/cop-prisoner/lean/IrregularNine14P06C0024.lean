import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0001

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1440 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 290, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 41 88 288 68 146 274), lower := (rows 7 98 133 41 88 288 68 128 256), losses := [] }

theorem u1440 : Upper (D 6) (R 6) [6,96,129,33,72,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1440
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1441 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 82, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 133 41 88 288 80 134 262), lower := (rows 7 98 133 41 88 288 80 128 256), losses := [] }

theorem u1441 : Upper (D 6) (R 6) [6,96,129,33,72,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1441
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1442 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 290, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 44 88 288 65 146 274), lower := (rows 7 98 133 44 88 288 65 128 256), losses := [] }

theorem u1442 : Upper (D 6) (R 6) [6,96,129,36,72,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1442
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1443 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 44 88 288 66 145 273), lower := (rows 7 98 133 44 88 288 66 128 256), losses := [] }

theorem u1443 : Upper (D 6) (R 6) [6,96,129,36,72,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1443
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1444 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 82, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 133 44 88 288 80 131 259), lower := (rows 7 98 133 44 88 288 80 128 256), losses := [] }

theorem u1444 : Upper (D 6) (R 6) [6,96,129,36,72,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1444
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1445 : PairBound 9 := { available := 72, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 98 133 44 274 48 65 200 328), lower := (rows 7 98 133 44 274 48 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 13 82 115 64 192 320), good := (rows 62 498 172 44 306 48 506 128 256) }] }

theorem u1445 : Upper (D 6) (R 6) [6,96,129,36,258,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1445
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1446 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5)], upper := (rows 7 98 133 44 274 48 72 193 321), lower := (rows 7 98 133 44 274 48 72 128 256), losses := [] }

theorem u1446 : Upper (D 6) (R 6) [6,96,129,36,258,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1446
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1447 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 280, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 98 133 56 274 36 65 200 328), lower := (rows 7 98 133 56 274 36 65 128 256), losses := [] }

theorem u1447 : Upper (D 6) (R 6) [6,96,129,48,258,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1447
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1448 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 56 274 36 72 193 321), lower := (rows 7 98 133 56 274 36 72 128 256), losses := [] }

theorem u1448 : Upper (D 6) (R 6) [6,96,129,48,258,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1448
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1449 : PairBound 9 := { available := 72, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 133 56 276 34 65 200 328), lower := (rows 7 98 133 56 276 34 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 77 17 99 64 194 322), good := (rows 446 490 188 56 284 418 506 128 256) }] }

theorem u1449 : Upper (D 6) (R 6) [6,96,129,48,260,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1449
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1450 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 106, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 56 276 34 72 193 321), lower := (rows 7 98 133 56 276 34 72 128 256), losses := [] }

theorem u1450 : Upper (D 6) (R 6) [6,96,129,48,260,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1450
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1451 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 280, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 98 133 56 280 36 65 194 322), lower := (rows 7 98 133 56 280 36 65 128 256), losses := [] }

theorem u1451 : Upper (D 6) (R 6) [6,96,129,48,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1451
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1452 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 133, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 98 133 56 280 36 66 193 321), lower := (rows 7 98 133 56 280 36 66 128 256), losses := [] }

theorem u1452 : Upper (D 6) (R 6) [6,96,129,48,264,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1452
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1453 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 280, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 98 133 56 336 36 65 138 266), lower := (rows 7 98 133 56 336 36 65 128 256), losses := [] }

theorem u1453 : Upper (D 6) (R 6) [6,96,129,48,320,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1453
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1454 : Route 9 := (fun mask => (mask,id))

def c1454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1454 : Upper (D 6) (R 6) [6,96,129,48,320,4,2] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,320,4,2] 13 (by decide) (choices 1) [1,8] r1454 c1454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u90
  · exact u91

def b1455 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 56 336 36 72 131 259), lower := (rows 7 98 133 56 336 36 72 128 256), losses := [] }

theorem u1455 : Upper (D 6) (R 6) [6,96,129,48,320,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1455
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1456 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 272, targets := 5 },{ cop := 3, region := 228, targets := 2 }], pairs := [(2,1),(4,0),(4,2)], upper := (rows 7 98 140 25 274 33 68 224 352), lower := (rows 7 98 140 25 274 33 68 128 256), losses := [] }

theorem u1456 : Upper (D 6) (R 6) [6,96,136,17,258,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1456
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1457 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 140 25 274 33 96 196 324), lower := (rows 7 98 140 25 274 33 96 128 256), losses := [] }

theorem u1457 : Upper (D 6) (R 6) [6,96,136,17,258,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1457
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1458 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 140 25 274 36 96 193 321), lower := (rows 7 98 140 25 274 36 96 128 256), losses := [] }

theorem u1458 : Upper (D 6) (R 6) [6,96,136,17,258,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1458
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1459 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 66, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 140 25 276 33 66 224 352), lower := (rows 7 98 140 25 276 33 66 128 256), losses := [{ target := 0, region := (rows 0 34 4 8 17 32 99 162 290), good := (rows 470 482 140 88 276 498 450 128 256) }] }

theorem u1459 : Upper (D 6) (R 6) [6,96,136,17,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1459
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1460 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 140 25 276 34 96 193 321), lower := (rows 7 98 140 25 276 34 96 128 256), losses := [] }

theorem u1460 : Upper (D 6) (R 6) [6,96,136,17,260,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1460
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1461 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 98 140 25 304 36 65 194 322), lower := (rows 7 98 140 25 304 36 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 8 83 37 64 194 322), good := (rows 438 498 172 56 304 36 498 128 256) }] }

theorem u1461 : Upper (D 6) (R 6) [6,96,136,17,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1461
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1462 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 66, targets := 5 }], pairs := [(1,0),(1,2),(2,5)], upper := (rows 7 98 140 25 304 36 66 193 321), lower := (rows 7 98 140 25 304 36 66 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 67 137 265), good := (rows 455 66 396 477 272 4 66 128 256) }] }

theorem u1462 : Upper (D 6) (R 6) [6,96,136,17,288,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1462
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1463 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 368, targets := 2 }], pairs := [(1,0),(2,0),(4,1)], upper := (rows 7 98 140 26 273 33 68 224 352), lower := (rows 7 98 140 26 273 33 68 128 256), losses := [{ target := 0, region := (rows 0 34 12 8 16 32 77 162 290), good := (rows 454 482 204 478 336 482 68 128 256) }] }

theorem u1463 : Upper (D 6) (R 6) [6,96,136,18,257,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1463
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1464 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 140 26 273 33 96 196 324), lower := (rows 7 98 140 26 273 33 96 128 256), losses := [] }

theorem u1464 : Upper (D 6) (R 6) [6,96,136,18,257,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1464
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1465 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 140 26 273 36 96 193 321), lower := (rows 7 98 140 26 273 36 96 128 256), losses := [] }

theorem u1465 : Upper (D 6) (R 6) [6,96,136,18,257,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1465
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1466 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 140 26 276 33 65 224 352), lower := (rows 7 98 140 26 276 33 65 128 256), losses := [] }

theorem u1466 : Upper (D 6) (R 6) [6,96,136,18,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1466
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1467 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 140 26 276 33 96 193 321), lower := (rows 7 98 140 26 276 33 96 128 256), losses := [] }

theorem u1467 : Upper (D 6) (R 6) [6,96,136,18,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1467
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1468 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 140 28 274 33 65 224 352), lower := (rows 7 98 140 28 274 33 65 128 256), losses := [] }

theorem u1468 : Upper (D 6) (R 6) [6,96,136,20,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1468
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1469 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 140 28 274 33 96 193 321), lower := (rows 7 98 140 28 274 33 96 128 256), losses := [] }

theorem u1469 : Upper (D 6) (R 6) [6,96,136,20,258,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1469
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1470 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 140 28 304 33 65 194 322), lower := (rows 7 98 140 28 304 33 65 128 256), losses := [] }

theorem u1470 : Upper (D 6) (R 6) [6,96,136,20,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1470
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1471 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 7 98 140 28 304 33 66 193 321), lower := (rows 7 98 140 28 304 33 66 128 256), losses := [] }

theorem u1471 : Upper (D 6) (R 6) [6,96,136,20,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1471
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1472 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 140 56 84 33 65 386 258), lower := (rows 7 98 140 56 84 33 65 128 256), losses := [] }

theorem u1472 : Upper (D 6) (R 6) [6,96,136,48,68,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1472
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1473 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 66, targets := 5 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 140 56 84 33 66 385 257), lower := (rows 7 98 140 56 84 33 66 128 256), losses := [] }

theorem u1473 : Upper (D 6) (R 6) [6,96,136,48,68,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1473
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1474 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 354, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,2),(4,5)], upper := (rows 7 98 140 56 84 33 320 131 259), lower := (rows 7 98 140 56 84 33 320 128 256), losses := [] }

theorem u1474 : Upper (D 6) (R 6) [6,96,136,48,68,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1474
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1475 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 140 56 274 33 65 196 324), lower := (rows 7 98 140 56 274 33 65 128 256), losses := [] }

theorem u1475 : Upper (D 6) (R 6) [6,96,136,48,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1475
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1476 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 32 }], pairs := [(1,0),(2,1),(4,5)], upper := (rows 7 98 140 56 274 33 68 193 321), lower := (rows 7 98 140 56 274 33 68 128 256), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 69 128 256), good := (rows 70 98 204 58 274 98 68 128 256) },{ target := 1, region := (rows 1 0 12 8 16 33 77 161 289), good := (rows 485 480 204 508 272 481 68 128 256) }] }

theorem u1476 : Upper (D 6) (R 6) [6,96,136,48,258,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1476
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1477 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 7 98 140 56 274 36 65 193 321), lower := (rows 7 98 140 56 274 36 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 8 16 37 64 128 256), good := (rows 38 98 172 56 274 36 98 128 256) }] }

theorem u1477 : Upper (D 6) (R 6) [6,96,136,48,258,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1477
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1478 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 140 56 276 33 65 194 322), lower := (rows 7 98 140 56 276 33 65 128 256), losses := [] }

theorem u1478 : Upper (D 6) (R 6) [6,96,136,48,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1478
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1479 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 66, targets := 5 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,0),(1,2),(4,5)], upper := (rows 7 98 140 56 276 33 66 193 321), lower := (rows 7 98 140 56 276 33 66 128 256), losses := [] }

theorem u1479 : Upper (D 6) (R 6) [6,96,136,48,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1479
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1480 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 140 56 336 33 65 134 262), lower := (rows 7 98 140 56 336 33 65 128 256), losses := [] }

theorem u1480 : Upper (D 6) (R 6) [6,96,136,48,320,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1480
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1481 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 5 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,0),(1,2),(4,5)], upper := (rows 7 98 140 56 336 33 66 133 261), lower := (rows 7 98 140 56 336 33 66 128 256), losses := [] }

theorem u1481 : Upper (D 6) (R 6) [6,96,136,48,320,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1481
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1482 : Route 9 := (fun mask => (mask,id))

def c1482 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1482 : Upper (D 6) (R 6) [6,96,136,48,320,1,4] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,320,1,4] 13 (by decide) (choices 1) [1,2] r1482 c1482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u92
  · exact u93

def b1483 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 7 98 140 56 336 36 65 131 259), lower := (rows 7 98 140 56 336 36 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 8 16 37 64 128 256), good := (rows 38 98 172 56 338 36 98 128 256) }] }

theorem u1483 : Upper (D 6) (R 6) [6,96,136,48,320,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1483
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1484 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 7 98 140 56 336 36 66 129 257), lower := (rows 7 98 140 56 336 36 66 128 256), losses := [] }

theorem u1484 : Upper (D 6) (R 6) [6,96,136,48,320,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1484
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1485 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 140 266 52 33 65 208 336), lower := (rows 7 98 140 266 52 33 65 128 256), losses := [] }

theorem u1485 : Upper (D 6) (R 6) [6,96,136,258,36,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1485
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1486 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 140 266 52 33 80 193 321), lower := (rows 7 98 140 266 52 33 80 128 256), losses := [] }

theorem u1486 : Upper (D 6) (R 6) [6,96,136,258,36,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1486
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1487 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 7 98 140 296 81 33 66 148 276), lower := (rows 7 98 140 296 81 33 66 128 256), losses := [] }

theorem u1487 : Upper (D 6) (R 6) [6,96,136,288,65,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1487
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1488 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 298, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,2),(3,2),(4,1)], upper := (rows 7 98 140 296 81 33 68 146 274), lower := (rows 7 98 140 296 81 33 68 128 256), losses := [] }

theorem u1488 : Upper (D 6) (R 6) [6,96,136,288,65,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1488
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1489 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 140 296 81 33 80 134 262), lower := (rows 7 98 140 296 81 33 80 128 256), losses := [] }

theorem u1489 : Upper (D 6) (R 6) [6,96,136,288,65,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1489
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1490 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 140 296 84 33 65 146 274), lower := (rows 7 98 140 296 84 33 65 128 256), losses := [] }

theorem u1490 : Upper (D 6) (R 6) [6,96,136,288,68,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1490
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1491 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 66, targets := 5 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 140 296 84 33 66 145 273), lower := (rows 7 98 140 296 84 33 66 128 256), losses := [] }

theorem u1491 : Upper (D 6) (R 6) [6,96,136,288,68,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1491
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1492 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 140 296 84 33 80 131 259), lower := (rows 7 98 140 296 84 33 80 128 256), losses := [] }

theorem u1492 : Upper (D 6) (R 6) [6,96,136,288,68,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1492
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1493 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 164, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 98 164 25 336 33 66 140 268), lower := (rows 7 98 164 25 336 33 66 128 256), losses := [] }

theorem u1493 : Upper (D 6) (R 6) [6,96,160,17,320,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1493
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1494 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 98 164 25 336 33 68 138 266), lower := (rows 7 98 164 25 336 33 68 128 256), losses := [] }

theorem u1494 : Upper (D 6) (R 6) [6,96,160,17,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1494
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1495 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 25 336 33 72 134 262), lower := (rows 7 98 164 25 336 33 72 128 256), losses := [] }

theorem u1495 : Upper (D 6) (R 6) [6,96,160,17,320,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1495
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1496 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 164 26 276 33 65 200 328), lower := (rows 7 98 164 26 276 33 65 128 256), losses := [] }

theorem u1496 : Upper (D 6) (R 6) [6,96,160,18,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1496
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1497 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 26 276 33 72 193 321), lower := (rows 7 98 164 26 276 33 72 128 256), losses := [] }

theorem u1497 : Upper (D 6) (R 6) [6,96,160,18,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1497
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1498 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 164 28 274 33 65 200 328), lower := (rows 7 98 164 28 274 33 65 128 256), losses := [] }

theorem u1498 : Upper (D 6) (R 6) [6,96,160,20,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1498
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1499 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 28 274 33 72 193 321), lower := (rows 7 98 164 28 274 33 72 128 256), losses := [] }

theorem u1499 : Upper (D 6) (R 6) [6,96,160,20,258,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1499
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1499
end Delivery.IrregularNine14.P06
