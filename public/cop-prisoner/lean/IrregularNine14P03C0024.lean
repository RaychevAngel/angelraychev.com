import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0003
import IrregularNine14P03C0004

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1440 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 403, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 76 176 96 209 145 401), lower := (rows 35 259 13 76 176 96 64 128 256), losses := [] }

theorem u1440 : Upper (D 3) (R 3) [34,257,9,68,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1440
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1441 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 13 76 176 160 81 209 337), lower := (rows 35 259 13 76 176 160 64 128 256), losses := [] }

theorem u1441 : Upper (D 3) (R 3) [34,257,9,68,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1441
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1442 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 259 13 88 145 36 224 224 480), lower := (rows 35 259 13 88 145 36 64 128 256), losses := [] }

theorem u1442 : Upper (D 3) (R 3) [34,257,9,80,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1442
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1443 : Route 9 := (fun mask => (mask,id))

def c1443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1443 : Upper (D 3) (R 3) [34,257,9,80,129,64] 13 := by
  apply FastRouting.sound _ _ [34,257,9,80,129,64] 13 (by decide) (choices 1) [4,32,128] r1443 c1443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u229
  · exact u230
  · exact u231

def r1444 : Route 9 := (fun mask => (mask,id))

def c1444 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1444 : Upper (D 3) (R 3) [34,257,9,80,129,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,80,129,128] 13 (by decide) (choices 1) [4,32] r1444 c1444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u232
  · exact u233

def b1445 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 88 148 33 224 224 480), lower := (rows 35 259 13 88 148 33 64 128 256), losses := [] }

theorem u1445 : Upper (D 3) (R 3) [34,257,9,80,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1445
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1446 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 88 148 96 225 161 417), lower := (rows 35 259 13 88 148 96 64 128 256), losses := [] }

theorem u1446 : Upper (D 3) (R 3) [34,257,9,80,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1446
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1447 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 13 88 148 160 97 225 353), lower := (rows 35 259 13 88 148 160 64 128 256), losses := [] }

theorem u1447 : Upper (D 3) (R 3) [34,257,9,80,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1447
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1448 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 200 52 33 208 208 464), lower := (rows 35 259 13 200 52 33 64 128 256), losses := [] }

theorem u1448 : Upper (D 3) (R 3) [34,257,9,192,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1448
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1449 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 259 13 200 52 48 193 193 449), lower := (rows 35 259 13 200 52 48 64 128 256), losses := [] }

theorem u1449 : Upper (D 3) (R 3) [34,257,9,192,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1449
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1450 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 200 52 96 209 145 401), lower := (rows 35 259 13 200 52 96 64 128 256), losses := [] }

theorem u1450 : Upper (D 3) (R 3) [34,257,9,192,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1450
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1451 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 35 259 13 200 81 36 240 176 432), lower := (rows 35 259 13 200 81 36 64 128 256), losses := [] }

theorem u1451 : Upper (D 3) (R 3) [34,257,9,192,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1451
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1452 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 35 259 13 200 81 48 228 164 420), lower := (rows 35 259 13 200 81 48 64 128 256), losses := [] }

theorem u1452 : Upper (D 3) (R 3) [34,257,9,192,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1452
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1453 : Route 9 := (fun mask => (mask,id))

def c1453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1453 : Upper (D 3) (R 3) [34,257,9,192,65,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,192,65,128] 13 (by decide) (choices 1) [4,16,32] r1453 c1453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u234
  · exact u235
  · exact u236

def b1454 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 200 112 33 212 148 404), lower := (rows 35 259 13 200 112 33 64 128 256), losses := [] }

theorem u1454 : Upper (D 3) (R 3) [34,257,9,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1454
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1455 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 259 13 200 112 36 209 145 401), lower := (rows 35 259 13 200 112 36 64 128 256), losses := [] }

theorem u1455 : Upper (D 3) (R 3) [34,257,9,192,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1455
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1456 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 259 13 200 112 48 197 133 389), lower := (rows 35 259 13 200 112 48 64 128 256), losses := [] }

theorem u1456 : Upper (D 3) (R 3) [34,257,9,192,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1456
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1457 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 35 259 13 200 112 160 85 149 277), lower := (rows 35 259 13 200 112 160 64 128 256), losses := [] }

theorem u1457 : Upper (D 3) (R 3) [34,257,9,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1457
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1458 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 259 28 73 145 36 224 224 480), lower := (rows 35 259 28 73 145 36 64 128 256), losses := [] }

theorem u1458 : Upper (D 3) (R 3) [34,257,24,65,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1458
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1459 : Route 9 := (fun mask => (mask,id))

def c1459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1459 : Upper (D 3) (R 3) [34,257,24,65,129,64] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,129,64] 13 (by decide) (choices 1) [4,32,128] r1459 c1459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u237
  · exact u238
  · exact u239

def b1460 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 28 73 148 33 224 224 480), lower := (rows 35 259 28 73 148 33 64 128 256), losses := [] }

theorem u1460 : Upper (D 3) (R 3) [34,257,24,65,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1460
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1461 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 28 73 148 96 225 161 417), lower := (rows 35 259 28 73 148 96 64 128 256), losses := [] }

theorem u1461 : Upper (D 3) (R 3) [34,257,24,65,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1461
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1462 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 28 73 148 160 97 225 353), lower := (rows 35 259 28 73 148 160 64 128 256), losses := [] }

theorem u1462 : Upper (D 3) (R 3) [34,257,24,65,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1462
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1463 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 28 73 176 33 196 196 452), lower := (rows 35 259 28 73 176 33 64 128 256), losses := [] }

theorem u1463 : Upper (D 3) (R 3) [34,257,24,65,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1463
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1464 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 259 28 73 176 36 193 193 449), lower := (rows 35 259 28 73 176 36 64 128 256), losses := [] }

theorem u1464 : Upper (D 3) (R 3) [34,257,24,65,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1464
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1465 : Route 9 := (fun mask => (mask,id))

def c1465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1465 : Upper (D 3) (R 3) [34,257,24,65,160,64] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,160,64] 13 (by decide) (choices 1) [1,4,128] r1465 c1465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u240
  · exact u241
  · exact u242

def b1466 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 28 73 176 160 69 197 325), lower := (rows 35 259 28 73 176 160 64 128 256), losses := [] }

theorem u1466 : Upper (D 3) (R 3) [34,257,24,65,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1466
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1467 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 35 259 44 73 145 36 208 208 464), lower := (rows 35 259 44 73 145 36 64 128 256), losses := [] }

theorem u1467 : Upper (D 3) (R 3) [34,257,40,65,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1467
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1468 : PairBound 9 := { available := 196, camps := [], pairs := [], upper := (rows 35 259 44 73 145 48 196 196 452), lower := (rows 35 259 44 73 145 48 64 128 256), losses := [] }

theorem u1468 : Upper (D 3) (R 3) [34,257,40,65,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1468
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1469 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 73 145 96 212 148 404), lower := (rows 35 259 44 73 145 96 64 128 256), losses := [] }

theorem u1469 : Upper (D 3) (R 3) [34,257,40,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1469
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1470 : Route 9 := (fun mask => (mask,id))

def c1470 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1470 : Upper (D 3) (R 3) [34,257,40,65,129,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,129,128] 13 (by decide) (choices 1) [4,16] r1470 c1470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u243
  · exact u244

def b1471 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 73 148 33 208 208 464), lower := (rows 35 259 44 73 148 33 64 128 256), losses := [] }

theorem u1471 : Upper (D 3) (R 3) [34,257,40,65,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1471
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1472 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 259 44 73 148 48 193 193 449), lower := (rows 35 259 44 73 148 48 64 128 256), losses := [] }

theorem u1472 : Upper (D 3) (R 3) [34,257,40,65,132,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1472
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1473 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 73 148 96 209 145 401), lower := (rows 35 259 44 73 148 96 64 128 256), losses := [] }

theorem u1473 : Upper (D 3) (R 3) [34,257,40,65,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1473
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1474 : Route 9 := (fun mask => (mask,id))

def c1474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1474 : Upper (D 3) (R 3) [34,257,40,65,132,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,132,128] 13 (by decide) (choices 1) [1,16] r1474 c1474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u245
  · exact u246

def b1475 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 73 208 33 212 148 404), lower := (rows 35 259 44 73 208 33 64 128 256), losses := [] }

theorem u1475 : Upper (D 3) (R 3) [34,257,40,65,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1475
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1476 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 259 44 73 208 36 209 145 401), lower := (rows 35 259 44 73 208 36 64 128 256), losses := [] }

theorem u1476 : Upper (D 3) (R 3) [34,257,40,65,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1476
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1477 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 259 44 73 208 48 197 133 389), lower := (rows 35 259 44 73 208 48 64 128 256), losses := [] }

theorem u1477 : Upper (D 3) (R 3) [34,257,40,65,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1477
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1478 : Route 9 := (fun mask => (mask,id))

def c1478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1478 : Upper (D 3) (R 3) [34,257,40,65,192,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,192,128] 13 (by decide) (choices 1) [1,4,16] r1478 c1478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u247
  · exact u248
  · exact u249

def b1479 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 88 145 33 196 196 452), lower := (rows 35 259 44 88 145 33 64 128 256), losses := [] }

theorem u1479 : Upper (D 3) (R 3) [34,257,40,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1479
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1480 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 259 44 88 145 36 193 193 449), lower := (rows 35 259 44 88 145 36 64 128 256), losses := [] }

theorem u1480 : Upper (D 3) (R 3) [34,257,40,80,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1480
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1481 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 88 145 96 197 133 389), lower := (rows 35 259 44 88 145 96 64 128 256), losses := [] }

theorem u1481 : Upper (D 3) (R 3) [34,257,40,80,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1481
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1482 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 44 88 145 160 69 197 325), lower := (rows 35 259 44 88 145 160 64 128 256), losses := [] }

theorem u1482 : Upper (D 3) (R 3) [34,257,40,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1482
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1483 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 200 81 33 212 148 404), lower := (rows 35 259 44 200 81 33 64 128 256), losses := [] }

theorem u1483 : Upper (D 3) (R 3) [34,257,40,192,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1483
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1484 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 259 44 200 81 36 209 145 401), lower := (rows 35 259 44 200 81 36 64 128 256), losses := [] }

theorem u1484 : Upper (D 3) (R 3) [34,257,40,192,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1484
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1485 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 259 44 200 81 48 197 133 389), lower := (rows 35 259 44 200 81 48 64 128 256), losses := [] }

theorem u1485 : Upper (D 3) (R 3) [34,257,40,192,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1485
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1486 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 44 200 81 160 85 149 277), lower := (rows 35 259 44 200 81 160 64 128 256), losses := [] }

theorem u1486 : Upper (D 3) (R 3) [34,257,40,192,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1486
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1487 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 35 259 69 88 145 36 232 168 424), lower := (rows 35 259 69 88 145 36 64 128 256), losses := [] }

theorem u1487 : Upper (D 3) (R 3) [34,257,65,80,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1487
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1488 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 35 259 69 88 145 40 228 164 420), lower := (rows 35 259 69 88 145 40 64 128 256), losses := [] }

theorem u1488 : Upper (D 3) (R 3) [34,257,65,80,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1488
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1489 : Route 9 := (fun mask => (mask,id))

def c1489 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1489 : Upper (D 3) (R 3) [34,257,65,80,129,128] 13 := by
  apply FastRouting.sound _ _ [34,257,65,80,129,128] 13 (by decide) (choices 1) [4,8,32] r1489 c1489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u250
  · exact u251
  · exact u252

def b1490 : PairBound 9 := { available := 140, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 69 88 176 33 204 140 396), lower := (rows 35 259 69 88 176 33 64 128 256), losses := [] }

theorem u1490 : Upper (D 3) (R 3) [34,257,65,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1490
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1491 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 35 259 69 88 176 36 201 137 393), lower := (rows 35 259 69 88 176 36 64 128 256), losses := [] }

theorem u1491 : Upper (D 3) (R 3) [34,257,65,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1491
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1492 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 259 69 88 176 40 197 133 389), lower := (rows 35 259 69 88 176 40 64 128 256), losses := [] }

theorem u1492 : Upper (D 3) (R 3) [34,257,65,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1492
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1493 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 69 88 176 160 77 141 269), lower := (rows 35 259 69 88 176 160 64 128 256), losses := [] }

theorem u1493 : Upper (D 3) (R 3) [34,257,65,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1493
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1494 : PairBound 9 := { available := 152, camps := [], pairs := [], upper := (rows 35 259 69 104 145 36 216 152 408), lower := (rows 35 259 69 104 145 36 64 128 256), losses := [] }

theorem u1494 : Upper (D 3) (R 3) [34,257,65,96,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1494
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1495 : PairBound 9 := { available := 148, camps := [], pairs := [], upper := (rows 35 259 69 104 145 40 212 148 404), lower := (rows 35 259 69 104 145 40 64 128 256), losses := [] }

theorem u1495 : Upper (D 3) (R 3) [34,257,65,96,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1495
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1496 : PairBound 9 := { available := 140, camps := [], pairs := [], upper := (rows 35 259 69 104 145 48 204 140 396), lower := (rows 35 259 69 104 145 48 64 128 256), losses := [] }

theorem u1496 : Upper (D 3) (R 3) [34,257,65,96,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1496
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1497 : Route 9 := (fun mask => (mask,id))

def c1497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1497 : Upper (D 3) (R 3) [34,257,65,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,257,65,96,129,128] 13 (by decide) (choices 1) [4,8,16] r1497 c1497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u253
  · exact u254
  · exact u255

def b1498 : PairBound 9 := { available := 152, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 69 104 148 33 216 152 408), lower := (rows 35 259 69 104 148 33 64 128 256), losses := [] }

theorem u1498 : Upper (D 3) (R 3) [34,257,65,96,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1498
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1499 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 259 69 104 148 40 209 145 401), lower := (rows 35 259 69 104 148 40 64 128 256), losses := [] }

theorem u1499 : Upper (D 3) (R 3) [34,257,65,96,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1499
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1499
end Delivery.IrregularNine14.P03
