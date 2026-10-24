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

def b1500 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 164 28 336 33 65 138 266), lower := (rows 7 98 164 28 336 33 65 128 256), losses := [] }

theorem u1500 : Upper (D 6) (R 6) [6,96,160,20,320,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1500
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1501 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 98 164 28 336 33 66 137 265), lower := (rows 7 98 164 28 336 33 66 128 256), losses := [] }

theorem u1501 : Upper (D 6) (R 6) [6,96,160,20,320,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1501
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1502 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 28 336 33 72 131 259), lower := (rows 7 98 164 28 336 33 72 128 256), losses := [] }

theorem u1502 : Upper (D 6) (R 6) [6,96,160,20,320,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1502
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1503 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 98 164 76 273 33 66 152 280), lower := (rows 7 98 164 76 273 33 66 128 256), losses := [] }

theorem u1503 : Upper (D 6) (R 6) [6,96,160,68,257,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1503
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1504 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 76 273 33 72 146 274), lower := (rows 7 98 164 76 273 33 72 128 256), losses := [] }

theorem u1504 : Upper (D 6) (R 6) [6,96,160,68,257,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1504
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1505 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 76 273 33 80 138 266), lower := (rows 7 98 164 76 273 33 80 128 256), losses := [] }

theorem u1505 : Upper (D 6) (R 6) [6,96,160,68,257,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1505
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1506 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 164 76 274 33 65 152 280), lower := (rows 7 98 164 76 274 33 65 128 256), losses := [] }

theorem u1506 : Upper (D 6) (R 6) [6,96,160,68,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1506
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1507 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 76 274 33 72 145 273), lower := (rows 7 98 164 76 274 33 72 128 256), losses := [] }

theorem u1507 : Upper (D 6) (R 6) [6,96,160,68,258,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1507
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1508 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 76 274 33 80 137 265), lower := (rows 7 98 164 76 274 33 80 128 256), losses := [] }

theorem u1508 : Upper (D 6) (R 6) [6,96,160,68,258,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1508
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1509 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 164 76 280 33 65 146 274), lower := (rows 7 98 164 76 280 33 65 128 256), losses := [] }

theorem u1509 : Upper (D 6) (R 6) [6,96,160,68,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1509
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1510 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 98 164 76 280 33 66 145 273), lower := (rows 7 98 164 76 280 33 66 128 256), losses := [] }

theorem u1510 : Upper (D 6) (R 6) [6,96,160,68,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1510
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1511 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 76 280 33 80 131 259), lower := (rows 7 98 164 76 280 33 80 128 256), losses := [] }

theorem u1511 : Upper (D 6) (R 6) [6,96,160,68,264,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1511
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1512 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 164 88 274 33 65 140 268), lower := (rows 7 98 164 88 274 33 65 128 256), losses := [] }

theorem u1512 : Upper (D 6) (R 6) [6,96,160,80,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1512
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1513 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 98 164 88 274 33 68 137 265), lower := (rows 7 98 164 88 274 33 68 128 256), losses := [] }

theorem u1513 : Upper (D 6) (R 6) [6,96,160,80,258,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1513
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1514 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 98 164 88 274 33 72 133 261), lower := (rows 7 98 164 88 274 33 72 128 256), losses := [] }

theorem u1514 : Upper (D 6) (R 6) [6,96,160,80,258,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1514
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1515 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 164 88 276 33 65 138 266), lower := (rows 7 98 164 88 276 33 65 128 256), losses := [] }

theorem u1515 : Upper (D 6) (R 6) [6,96,160,80,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1515
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1516 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 98 164 88 276 33 66 137 265), lower := (rows 7 98 164 88 276 33 66 128 256), losses := [] }

theorem u1516 : Upper (D 6) (R 6) [6,96,160,80,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1516
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1517 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 98 164 88 276 33 72 131 259), lower := (rows 7 98 164 88 276 33 72 128 256), losses := [] }

theorem u1517 : Upper (D 6) (R 6) [6,96,160,80,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1517
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1518 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 98 388 44 88 33 65 146 274), lower := (rows 7 98 388 44 88 33 65 128 256), losses := [] }

theorem u1518 : Upper (D 6) (R 6) [6,96,384,36,72,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1518
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1519 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 82, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 388 44 88 33 66 145 273), lower := (rows 7 98 388 44 88 33 66 128 256), losses := [] }

theorem u1519 : Upper (D 6) (R 6) [6,96,384,36,72,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1519
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1520 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 82, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 388 44 88 33 80 131 259), lower := (rows 7 98 388 44 88 33 80 128 256), losses := [] }

theorem u1520 : Upper (D 6) (R 6) [6,96,384,36,72,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1520
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1521 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 131 261 26 52 96 72 224 352), lower := (rows 7 131 261 26 52 96 72 128 256), losses := [] }

theorem u1521 : Upper (D 6) (R 6) [6,129,257,18,36,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1521
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1522 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 120, targets := 1 },{ cop := 0, region := 112, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 131 261 26 52 96 96 200 328), lower := (rows 7 131 261 26 52 96 96 128 256), losses := [] }

theorem u1522 : Upper (D 6) (R 6) [6,129,257,18,36,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1522
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1523 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 131 261 26 112 36 72 224 352), lower := (rows 7 131 261 26 112 36 72 128 256), losses := [] }

theorem u1523 : Upper (D 6) (R 6) [6,129,257,18,96,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1523
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1524 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 131 261 26 112 36 96 200 328), lower := (rows 7 131 261 26 112 36 96 128 256), losses := [] }

theorem u1524 : Upper (D 6) (R 6) [6,129,257,18,96,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1524
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1525 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 131 261 42 52 96 72 208 336), lower := (rows 7 131 261 42 52 96 72 128 256), losses := [] }

theorem u1525 : Upper (D 6) (R 6) [6,129,257,34,36,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1525
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1526 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 407, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 261 42 84 40 96 208 336), lower := (rows 7 131 261 42 84 40 96 128 256), losses := [] }

theorem u1526 : Upper (D 6) (R 6) [6,129,257,34,68,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1526
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1527 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 131 261 42 84 48 96 200 328), lower := (rows 7 131 261 42 84 48 96 128 256), losses := [] }

theorem u1527 : Upper (D 6) (R 6) [6,129,257,34,68,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1527
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1528 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 120, targets := 1 },{ cop := 0, region := 112, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 131 261 42 84 96 96 152 280), lower := (rows 7 131 261 42 84 96 96 128 256), losses := [] }

theorem u1528 : Upper (D 6) (R 6) [6,129,257,34,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1528
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1529 : Route 9 := (fun mask => (mask,id))

def c1529 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1529 : Upper (D 6) (R 6) [6,129,257,34,72,64,4] 13 := by
  apply FastRouting.sound _ _ [6,129,257,34,72,64,4] 13 (by decide) (choices 1) [16,32] r1529 c1529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u94
  · exact u95

def b1530 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 120, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 131 261 42 88 96 80 164 292), lower := (rows 7 131 261 42 88 96 80 128 256), losses := [] }

theorem u1530 : Upper (D 6) (R 6) [6,129,257,34,72,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1530
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1531 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 391, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 131 261 42 88 96 96 148 276), lower := (rows 7 131 261 42 88 96 96 128 256), losses := [] }

theorem u1531 : Upper (D 6) (R 6) [6,129,257,34,72,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1531
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1532 : Route 9 := (fun mask => (mask,id))

def c1532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1532 : Upper (D 6) (R 6) [6,129,257,48,72,2,4] 13 := by
  apply FastRouting.sound _ _ [6,129,257,48,72,2,4] 13 (by decide) (choices 1) [32,64] r1532 c1532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u96
  · exact u97

def b1533 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 88, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 131 261 56 88 34 96 196 324), lower := (rows 7 131 261 56 88 34 96 128 256), losses := [] }

theorem u1533 : Upper (D 6) (R 6) [6,129,257,48,72,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1533
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1534 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 112, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 268 25 112 34 68 224 352), lower := (rows 7 131 268 25 112 34 68 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 35 77 155 283), good := (rows 502 498 476 508 496 434 68 128 256) },{ target := 1, region := (rows 1 0 12 8 16 32 77 144 272), good := (rows 69 193 332 477 496 32 68 128 256) }] }

theorem u1534 : Upper (D 6) (R 6) [6,129,264,17,96,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1534
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1535 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 131 268 25 112 34 96 196 324), lower := (rows 7 131 268 25 112 34 96 128 256), losses := [] }

theorem u1535 : Upper (D 6) (R 6) [6,129,264,17,96,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1535
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1536 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 131 268 25 112 36 96 194 322), lower := (rows 7 131 268 25 112 36 96 128 256), losses := [] }

theorem u1536 : Upper (D 6) (R 6) [6,129,264,17,96,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1536
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1537 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 112, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 7 131 268 26 112 33 68 224 352), lower := (rows 7 131 268 26 112 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 48 32 77 176 304), good := (rows 70 194 332 478 496 496 68 128 256) }] }

theorem u1537 : Upper (D 6) (R 6) [6,129,264,18,96,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1537
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1538 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 131 268 26 112 33 96 196 324), lower := (rows 7 131 268 26 112 33 96 128 256), losses := [] }

theorem u1538 : Upper (D 6) (R 6) [6,129,264,18,96,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1538
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1539 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 131 268 26 112 36 96 193 321), lower := (rows 7 131 268 26 112 36 96 128 256), losses := [] }

theorem u1539 : Upper (D 6) (R 6) [6,129,264,18,96,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1539
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1540 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 268, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 268 28 112 33 66 224 352), lower := (rows 7 131 268 28 112 33 66 128 256), losses := [] }

theorem u1540 : Upper (D 6) (R 6) [6,129,264,20,96,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1540
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1541 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 131 268 28 112 33 96 194 322), lower := (rows 7 131 268 28 112 33 96 128 256), losses := [] }

theorem u1541 : Upper (D 6) (R 6) [6,129,264,20,96,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1541
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1542 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 131 268 28 112 34 96 193 321), lower := (rows 7 131 268 28 112 34 96 128 256), losses := [] }

theorem u1542 : Upper (D 6) (R 6) [6,129,264,20,96,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1542
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1543 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 112, targets := 1 },{ cop := 0, region := 104, targets := 2 }], pairs := [(2,0),(3,1),(4,0)], upper := (rows 7 131 268 41 50 96 68 208 336), lower := (rows 7 131 268 41 50 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 111 77 139 267), good := (rows 502 498 492 508 434 96 100 128 256) }] }

theorem u1543 : Upper (D 6) (R 6) [6,129,264,33,34,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1543
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1544 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 120, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 131 268 41 50 96 80 196 324), lower := (rows 7 131 268 41 50 96 80 128 256), losses := [] }

theorem u1544 : Upper (D 6) (R 6) [6,129,264,33,34,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1544
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1545 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 104, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,1),(4,0),(4,5)], upper := (rows 7 131 268 41 82 96 68 176 304), lower := (rows 7 131 268 41 82 96 68 128 256), losses := [] }

theorem u1545 : Upper (D 6) (R 6) [6,129,264,33,66,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1545
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1546 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 268 41 82 96 80 164 292), lower := (rows 7 131 268 41 82 96 80 128 256), losses := [] }

theorem u1546 : Upper (D 6) (R 6) [6,129,264,33,66,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1546
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1547 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 0, region := 112, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 7 131 268 41 82 96 96 148 276), lower := (rows 7 131 268 41 82 96 96 128 256), losses := [] }

theorem u1547 : Upper (D 6) (R 6) [6,129,264,33,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1547
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1548 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 104, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,2),(4,0),(4,5)], upper := (rows 7 131 268 41 84 96 66 176 304), lower := (rows 7 131 268 41 84 96 66 128 256), losses := [] }

theorem u1548 : Upper (D 6) (R 6) [6,129,264,33,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1548
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1549 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 268 41 84 96 80 162 290), lower := (rows 7 131 268 41 84 96 80 128 256), losses := [] }

theorem u1549 : Upper (D 6) (R 6) [6,129,264,33,68,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1549
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1550 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 131 268 41 84 96 96 146 274), lower := (rows 7 131 268 41 84 96 96 128 256), losses := [] }

theorem u1550 : Upper (D 6) (R 6) [6,129,264,33,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1550
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1551 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 104, targets := 1 },{ cop := 0, region := 112, targets := 2 }], pairs := [(2,0),(3,0),(4,1)], upper := (rows 7 131 268 42 49 96 68 208 336), lower := (rows 7 131 268 42 49 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 20 11 16 119 85 144 272), good := (rows 110 234 364 42 508 96 100 128 256) }] }

theorem u1551 : Upper (D 6) (R 6) [6,129,264,34,33,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1551
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1552 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 120, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 131 268 42 49 96 80 196 324), lower := (rows 7 131 268 42 49 96 80 128 256), losses := [] }

theorem u1552 : Upper (D 6) (R 6) [6,129,264,34,33,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1552
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1553 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 170, targets := 4 },{ cop := 0, region := 104, targets := 1 }], pairs := [(1,2),(3,0),(3,2)], upper := (rows 7 131 268 42 81 96 68 176 304), lower := (rows 7 131 268 42 81 96 68 128 256), losses := [] }

theorem u1553 : Upper (D 6) (R 6) [6,129,264,34,65,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1553
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1554 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 268 42 81 96 80 164 292), lower := (rows 7 131 268 42 81 96 80 128 256), losses := [] }

theorem u1554 : Upper (D 6) (R 6) [6,129,264,34,65,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1554
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1555 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 0, region := 104, targets := 1 }], pairs := [(3,0),(3,2),(4,2)], upper := (rows 7 131 268 42 81 96 96 148 276), lower := (rows 7 131 268 42 81 96 96 128 256), losses := [] }

theorem u1555 : Upper (D 6) (R 6) [6,129,264,34,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1555
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1556 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 2 },{ cop := 0, region := 104, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,2),(4,1),(4,5)], upper := (rows 7 131 268 42 84 96 65 176 304), lower := (rows 7 131 268 42 84 96 65 128 256), losses := [] }

theorem u1556 : Upper (D 6) (R 6) [6,129,264,34,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1556
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1557 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 268 42 84 96 80 161 289), lower := (rows 7 131 268 42 84 96 80 128 256), losses := [] }

theorem u1557 : Upper (D 6) (R 6) [6,129,264,34,68,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1557
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1558 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 131 268 42 84 96 96 145 273), lower := (rows 7 131 268 42 84 96 96 128 256), losses := [] }

theorem u1558 : Upper (D 6) (R 6) [6,129,264,34,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1558
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1559 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 242, targets := 4 },{ cop := 0, region := 104, targets := 2 }], pairs := [(1,2),(3,1),(4,2)], upper := (rows 7 131 268 44 50 96 65 208 336), lower := (rows 7 131 268 44 50 96 65 128 256), losses := [] }

theorem u1559 : Upper (D 6) (R 6) [6,129,264,36,34,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1559
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1559
end Delivery.IrregularNine14.P06
