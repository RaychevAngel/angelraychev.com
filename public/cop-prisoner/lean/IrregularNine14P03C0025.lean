import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0004

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1500 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 35 259 69 104 148 48 201 137 393), lower := (rows 35 259 69 104 148 48 64 128 256), losses := [] }

theorem u1500 : Upper (D 3) (R 3) [34,257,65,96,132,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1500
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1501 : Route 9 := (fun mask => (mask,id))

def c1501 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1501 : Upper (D 3) (R 3) [34,257,65,96,132,128] 13 := by
  apply FastRouting.sound _ _ [34,257,65,96,132,128] 13 (by decide) (choices 1) [1,8,16] r1501 c1501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u256
  · exact u257
  · exact u258

def b1502 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 69 104 152 33 212 148 404), lower := (rows 35 259 69 104 152 33 64 128 256), losses := [] }

theorem u1502 : Upper (D 3) (R 3) [34,257,65,96,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1502
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1503 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 259 69 104 152 36 209 145 401), lower := (rows 35 259 69 104 152 36 64 128 256), losses := [] }

theorem u1503 : Upper (D 3) (R 3) [34,257,65,96,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1503
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1504 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 259 69 104 152 48 197 133 389), lower := (rows 35 259 69 104 152 48 64 128 256), losses := [] }

theorem u1504 : Upper (D 3) (R 3) [34,257,65,96,136,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1504
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1505 : Route 9 := (fun mask => (mask,id))

def c1505 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1505 : Upper (D 3) (R 3) [34,257,65,96,136,128] 13 := by
  apply FastRouting.sound _ _ [34,257,65,96,136,128] 13 (by decide) (choices 1) [1,4,16] r1505 c1505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u259
  · exact u260
  · exact u261

def b1506 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 35 259 69 137 208 36 120 184 312), lower := (rows 35 259 69 137 208 36 64 128 256), losses := [] }

theorem u1506 : Upper (D 3) (R 3) [34,257,65,129,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1506
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1507 : PairBound 9 := { available := 44, camps := [], pairs := [], upper := (rows 35 259 69 137 208 48 108 172 300), lower := (rows 35 259 69 137 208 48 64 128 256), losses := [] }

theorem u1507 : Upper (D 3) (R 3) [34,257,65,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1507
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1508 : PairBound 9 := { available := 88, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 69 140 176 33 88 216 344), lower := (rows 35 259 69 140 176 33 64 128 256), losses := [] }

theorem u1508 : Upper (D 3) (R 3) [34,257,65,132,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1508
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1509 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 259 69 140 176 40 81 209 337), lower := (rows 35 259 69 140 176 40 64 128 256), losses := [] }

theorem u1509 : Upper (D 3) (R 3) [34,257,65,132,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1509
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1510 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 35 259 69 140 176 48 73 201 329), lower := (rows 35 259 69 140 176 48 64 128 256), losses := [] }

theorem u1510 : Upper (D 3) (R 3) [34,257,65,132,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1510
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1511 : PairBound 9 := { available := 25, camps := [], pairs := [(4,0)], upper := (rows 35 259 69 140 176 96 89 153 281), lower := (rows 35 259 69 140 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 100 64 128 256), good := (rows 34 258 100 188 176 96 96 128 256) }] }

theorem u1511 : Upper (D 3) (R 3) [34,257,65,132,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1511
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1512 : PairBound 9 := { available := 56, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 69 140 208 33 120 184 312), lower := (rows 35 259 69 140 208 33 64 128 256), losses := [] }

theorem u1512 : Upper (D 3) (R 3) [34,257,65,132,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1512
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1513 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 259 69 140 208 40 113 177 305), lower := (rows 35 259 69 140 208 40 64 128 256), losses := [] }

theorem u1513 : Upper (D 3) (R 3) [34,257,65,132,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1513
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1514 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 259 69 140 208 48 105 169 297), lower := (rows 35 259 69 140 208 48 64 128 256), losses := [] }

theorem u1514 : Upper (D 3) (R 3) [34,257,65,132,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1514
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1515 : PairBound 9 := { available := 28, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 69 168 208 33 92 156 284), lower := (rows 35 259 69 168 208 33 64 128 256), losses := [] }

theorem u1515 : Upper (D 3) (R 3) [34,257,65,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1515
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1516 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 35 259 69 168 208 36 89 153 281), lower := (rows 35 259 69 168 208 36 64 128 256), losses := [] }

theorem u1516 : Upper (D 3) (R 3) [34,257,65,160,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1516
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1517 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 35 259 69 168 208 40 85 149 277), lower := (rows 35 259 69 168 208 40 64 128 256), losses := [] }

theorem u1517 : Upper (D 3) (R 3) [34,257,65,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1517
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1518 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 35 259 69 168 208 48 77 141 269), lower := (rows 35 259 69 168 208 48 64 128 256), losses := [] }

theorem u1518 : Upper (D 3) (R 3) [34,257,65,160,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1518
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1519 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 168 208 33 85 149 277), lower := (rows 35 259 76 168 208 33 64 128 256), losses := [] }

theorem u1519 : Upper (D 3) (R 3) [34,257,72,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1519
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1520 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 259 76 168 208 36 81 145 273), lower := (rows 35 259 76 168 208 36 64 128 256), losses := [] }

theorem u1520 : Upper (D 3) (R 3) [34,257,72,160,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1520
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1521 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 259 76 168 208 48 69 133 261), lower := (rows 35 259 76 168 208 48 64 128 256), losses := [] }

theorem u1521 : Upper (D 3) (R 3) [34,257,72,160,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1521
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1522 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 13 88 145 33 224 224 480), lower := (rows 35 262 13 88 145 33 64 128 256), losses := [] }

theorem u1522 : Upper (D 3) (R 3) [34,260,9,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1522
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1523 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 13 88 145 96 225 161 417), lower := (rows 35 262 13 88 145 96 64 128 256), losses := [] }

theorem u1523 : Upper (D 3) (R 3) [34,260,9,80,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1523
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1524 : PairBound 9 := { available := 97, camps := [], pairs := [(1,7)], upper := (rows 35 262 13 88 145 160 97 225 353), lower := (rows 35 262 13 88 145 160 64 128 256), losses := [{ target := 7, region := (rows 1 22 20 24 16 32 65 0 257), good := (rows 355 262 335 94 351 32 64 0 256) }] }

theorem u1524 : Upper (D 3) (R 3) [34,260,9,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1524
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1525 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 13 200 81 33 240 176 432), lower := (rows 35 262 13 200 81 33 64 128 256), losses := [] }

theorem u1525 : Upper (D 3) (R 3) [34,260,9,192,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1525
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1526 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 262 13 200 81 48 225 161 417), lower := (rows 35 262 13 200 81 48 64 128 256), losses := [] }

theorem u1526 : Upper (D 3) (R 3) [34,260,9,192,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1526
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1527 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 262 13 200 81 160 113 177 305), lower := (rows 35 262 13 200 81 160 64 128 256), losses := [] }

theorem u1527 : Upper (D 3) (R 3) [34,260,9,192,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1527
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1528 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 13 200 112 33 209 145 401), lower := (rows 35 262 13 200 112 33 64 128 256), losses := [] }

theorem u1528 : Upper (D 3) (R 3) [34,260,9,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1528
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1529 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 262 13 200 112 48 193 129 385), lower := (rows 35 262 13 200 112 48 64 128 256), losses := [] }

theorem u1529 : Upper (D 3) (R 3) [34,260,9,192,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1529
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1530 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 262 13 200 112 160 81 145 273), lower := (rows 35 262 13 200 112 160 64 128 256), losses := [] }

theorem u1530 : Upper (D 3) (R 3) [34,260,9,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1530
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1531 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 28 73 145 33 224 224 480), lower := (rows 35 262 28 73 145 33 64 128 256), losses := [] }

theorem u1531 : Upper (D 3) (R 3) [34,260,24,65,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1531
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1532 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 28 73 145 96 225 161 417), lower := (rows 35 262 28 73 145 96 64 128 256), losses := [] }

theorem u1532 : Upper (D 3) (R 3) [34,260,24,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1532
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1533 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 69 25 152 33 224 224 480), lower := (rows 35 262 69 25 152 33 64 128 256), losses := [] }

theorem u1533 : Upper (D 3) (R 3) [34,260,65,17,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1533
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1534 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 69 25 152 96 225 161 417), lower := (rows 35 262 69 25 152 96 64 128 256), losses := [] }

theorem u1534 : Upper (D 3) (R 3) [34,260,65,17,136,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1534
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1535 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 69 25 152 160 97 225 353), lower := (rows 35 262 69 25 152 160 64 128 256), losses := [] }

theorem u1535 : Upper (D 3) (R 3) [34,260,65,17,136,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1535
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1536 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 69 25 208 33 232 168 424), lower := (rows 35 262 69 25 208 33 64 128 256), losses := [] }

theorem u1536 : Upper (D 3) (R 3) [34,260,65,17,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1536
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1537 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 262 69 25 208 40 225 161 417), lower := (rows 35 262 69 25 208 40 64 128 256), losses := [] }

theorem u1537 : Upper (D 3) (R 3) [34,260,65,17,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1537
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1538 : Route 9 := (fun mask => (mask,id))

def c1538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1538 : Upper (D 3) (R 3) [34,260,65,17,192,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17,192,128] 13 (by decide) (choices 1) [1,8,32] r1538 c1538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u262
  · exact u263
  · exact u264

def b1539 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 69 56 145 33 200 200 456), lower := (rows 35 262 69 56 145 33 64 128 256), losses := [] }

theorem u1539 : Upper (D 3) (R 3) [34,260,65,48,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1539
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1540 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 262 69 56 145 40 193 193 449), lower := (rows 35 262 69 56 145 40 64 128 256), losses := [] }

theorem u1540 : Upper (D 3) (R 3) [34,260,65,48,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1540
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1541 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 69 56 145 96 201 137 393), lower := (rows 35 262 69 56 145 96 64 128 256), losses := [] }

theorem u1541 : Upper (D 3) (R 3) [34,260,65,48,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1541
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1542 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 69 56 145 160 73 201 329), lower := (rows 35 262 69 56 145 160 64 128 256), losses := [] }

theorem u1542 : Upper (D 3) (R 3) [34,260,65,48,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1542
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1543 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 69 56 208 33 201 137 393), lower := (rows 35 262 69 56 208 33 64 128 256), losses := [] }

theorem u1543 : Upper (D 3) (R 3) [34,260,65,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1543
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1544 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 262 69 56 208 40 193 129 385), lower := (rows 35 262 69 56 208 40 64 128 256), losses := [] }

theorem u1544 : Upper (D 3) (R 3) [34,260,65,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1544
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1545 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 69 56 208 160 73 137 265), lower := (rows 35 262 69 56 208 160 64 128 256), losses := [] }

theorem u1545 : Upper (D 3) (R 3) [34,260,65,48,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1545
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1546 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 69 88 145 33 232 168 424), lower := (rows 35 262 69 88 145 33 64 128 256), losses := [] }

theorem u1546 : Upper (D 3) (R 3) [34,260,65,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1546
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1547 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 262 69 88 145 40 225 161 417), lower := (rows 35 262 69 88 145 40 64 128 256), losses := [] }

theorem u1547 : Upper (D 3) (R 3) [34,260,65,80,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1547
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1548 : Route 9 := (fun mask => (mask,id))

def c1548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1548 : Upper (D 3) (R 3) [34,260,65,80,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,80,129,128] 13 (by decide) (choices 1) [1,8,32] r1548 c1548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u265
  · exact u266
  · exact u267

def b1549 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 69 88 176 33 201 137 393), lower := (rows 35 262 69 88 176 33 64 128 256), losses := [] }

theorem u1549 : Upper (D 3) (R 3) [34,260,65,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1549
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1550 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 262 69 88 176 40 193 129 385), lower := (rows 35 262 69 88 176 40 64 128 256), losses := [] }

theorem u1550 : Upper (D 3) (R 3) [34,260,65,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1550
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1551 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 69 88 176 160 73 137 265), lower := (rows 35 262 69 88 176 160 64 128 256), losses := [] }

theorem u1551 : Upper (D 3) (R 3) [34,260,65,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1551
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1552 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 69 104 145 33 216 152 408), lower := (rows 35 262 69 104 145 33 64 128 256), losses := [] }

theorem u1552 : Upper (D 3) (R 3) [34,260,65,96,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1552
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1553 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 262 69 104 145 40 209 145 401), lower := (rows 35 262 69 104 145 40 64 128 256), losses := [] }

theorem u1553 : Upper (D 3) (R 3) [34,260,65,96,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1553
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1554 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 35 262 69 104 145 48 201 137 393), lower := (rows 35 262 69 104 145 48 64 128 256), losses := [] }

theorem u1554 : Upper (D 3) (R 3) [34,260,65,96,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1554
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1555 : Route 9 := (fun mask => (mask,id))

def c1555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1555 : Upper (D 3) (R 3) [34,260,65,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96,129,128] 13 (by decide) (choices 1) [1,8,16] r1555 c1555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u268
  · exact u269
  · exact u270

def b1556 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 69 104 152 33 209 145 401), lower := (rows 35 262 69 104 152 33 64 128 256), losses := [] }

theorem u1556 : Upper (D 3) (R 3) [34,260,65,96,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1556
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1557 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 262 69 104 152 48 193 129 385), lower := (rows 35 262 69 104 152 48 64 128 256), losses := [] }

theorem u1557 : Upper (D 3) (R 3) [34,260,65,96,136,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1557
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1558 : Route 9 := (fun mask => (mask,id))

def c1558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1558 : Upper (D 3) (R 3) [34,260,65,96,136,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96,136,128] 13 (by decide) (choices 1) [1,16] r1558 c1558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u271
  · exact u272

def b1559 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 69 137 176 33 88 216 344), lower := (rows 35 262 69 137 176 33 64 128 256), losses := [] }

theorem u1559 : Upper (D 3) (R 3) [34,260,65,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1559
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1559
end Delivery.IrregularNine14.P03
