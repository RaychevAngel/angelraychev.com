import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0006
import IrregularNine14P00C0007

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1440 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 51 194 76 152 272 37 101 165 293), lower := (rows 51 194 76 152 272 32 64 128 256), losses := [] }

theorem u1440 : Upper (D 0) (R 0) [50,192,72,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1440
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1441 : Route 9 := (fun mask => (mask,id))

def c1441 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1441 : Upper (D 0) (R 0) [50,192,72,257,1] 13 := by
  apply FastRouting.sound _ _ [50,192,72,257,1] 13 (by decide) (choices 1) [4,16,128] r1441 c1441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u405
  · exact u406
  · exact u407

def b1442 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 194 76 265 20 177 241 177 433), lower := (rows 51 194 76 265 20 32 64 128 256), losses := [] }

theorem u1442 : Upper (D 0) (R 0) [50,192,72,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1442
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1443 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 76 265 48 181 213 149 405), lower := (rows 51 194 76 265 48 32 64 128 256), losses := [] }

theorem u1443 : Upper (D 0) (R 0) [50,192,72,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1443
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1444 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 76 265 144 53 117 181 309), lower := (rows 51 194 76 265 144 32 64 128 256), losses := [] }

theorem u1444 : Upper (D 0) (R 0) [50,192,72,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1444
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1445 : Route 9 := (fun mask => (mask,id))

def c1445 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1445 : Upper (D 0) (R 0) [50,192,72,272,1] 13 := by
  apply FastRouting.sound _ _ [50,192,72,272,1] 13 (by decide) (choices 1) [1,4,128] r1445 c1445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u408
  · exact u409
  · exact u410

def b1446 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 194 76 280 20 161 225 161 417), lower := (rows 51 194 76 280 20 32 64 128 256), losses := [] }

theorem u1446 : Upper (D 0) (R 0) [50,192,72,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1446
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1447 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 76 280 48 165 197 133 389), lower := (rows 51 194 76 280 48 32 64 128 256), losses := [] }

theorem u1447 : Upper (D 0) (R 0) [50,192,72,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1447
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1448 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 76 280 144 37 101 165 293), lower := (rows 51 194 76 280 144 32 64 128 256), losses := [] }

theorem u1448 : Upper (D 0) (R 0) [50,192,72,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1448
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1449 : Route 9 := (fun mask => (mask,id))

def c1449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1449 : Upper (D 0) (R 0) [50,192,72,384,1] 13 := by
  apply FastRouting.sound _ _ [50,192,72,384,1] 13 (by decide) (choices 1) [1,4,16] r1449 c1449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u411
  · exact u412
  · exact u413

def b1450 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 51 194 76 392 20 49 113 177 305), lower := (rows 51 194 76 392 20 32 64 128 256), losses := [] }

theorem u1450 : Upper (D 0) (R 0) [50,192,72,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1450
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1451 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 76 392 48 53 85 149 277), lower := (rows 51 194 76 392 48 32 64 128 256), losses := [] }

theorem u1451 : Upper (D 0) (R 0) [50,192,72,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1451
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1452 : Route 9 := (fun mask => (mask,id))

def c1452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1452 : Upper (D 0) (R 0) [50,192,80,160,1] 13 := by
  apply FastRouting.sound _ _ [50,192,80,160,1] 13 (by decide) (choices 1) [1,4,8,256] r1452 c1452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u414
  · exact u415
  · exact u416
  · exact u417

def b1453 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 51 194 84 168 20 297 329 393 265), lower := (rows 51 194 84 168 20 32 64 128 256), losses := [] }

theorem u1453 : Upper (D 0) (R 0) [50,192,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1453
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1454 : PairBound 9 := { available := 261, camps := [], pairs := [], upper := (rows 51 194 84 168 24 293 325 389 261), lower := (rows 51 194 84 168 24 32 64 128 256), losses := [] }

theorem u1454 : Upper (D 0) (R 0) [50,192,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1454
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1455 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 51 194 84 168 272 45 77 141 269), lower := (rows 51 194 84 168 272 32 64 128 256), losses := [] }

theorem u1455 : Upper (D 0) (R 0) [50,192,80,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1455
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1456 : Route 9 := (fun mask => (mask,id))

def c1456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1456 : Upper (D 0) (R 0) [50,192,80,257,1] 13 := by
  apply FastRouting.sound _ _ [50,192,80,257,1] 13 (by decide) (choices 1) [4,8,128] r1456 c1456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u418
  · exact u419
  · exact u420

def b1457 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 51 194 84 265 20 169 233 169 425), lower := (rows 51 194 84 265 20 32 64 128 256), losses := [] }

theorem u1457 : Upper (D 0) (R 0) [50,192,80,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1457
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1458 : PairBound 9 := { available := 165, camps := [], pairs := [], upper := (rows 51 194 84 265 24 165 229 165 421), lower := (rows 51 194 84 265 24 32 64 128 256), losses := [] }

theorem u1458 : Upper (D 0) (R 0) [50,192,80,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1458
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1459 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 84 265 48 173 205 141 397), lower := (rows 51 194 84 265 48 32 64 128 256), losses := [] }

theorem u1459 : Upper (D 0) (R 0) [50,192,80,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1459
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1460 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 84 265 144 45 109 173 301), lower := (rows 51 194 84 265 144 32 64 128 256), losses := [] }

theorem u1460 : Upper (D 0) (R 0) [50,192,80,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1460
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1461 : Route 9 := (fun mask => (mask,id))

def c1461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1461 : Upper (D 0) (R 0) [50,192,80,260,1] 13 := by
  apply FastRouting.sound _ _ [50,192,80,260,1] 13 (by decide) (choices 1) [1,8,128] r1461 c1461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u421
  · exact u422
  · exact u423

def b1462 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 194 84 268 24 161 225 161 417), lower := (rows 51 194 84 268 24 32 64 128 256), losses := [] }

theorem u1462 : Upper (D 0) (R 0) [50,192,80,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1462
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1463 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 84 268 48 169 201 137 393), lower := (rows 51 194 84 268 48 32 64 128 256), losses := [] }

theorem u1463 : Upper (D 0) (R 0) [50,192,80,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1463
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1464 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 84 268 144 41 105 169 297), lower := (rows 51 194 84 268 144 32 64 128 256), losses := [] }

theorem u1464 : Upper (D 0) (R 0) [50,192,80,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1464
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1465 : Route 9 := (fun mask => (mask,id))

def c1465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1465 : Upper (D 0) (R 0) [50,192,80,288,1] 13 := by
  apply FastRouting.sound _ _ [50,192,80,288,1] 13 (by decide) (choices 1) [1,4,8,128] r1465 c1465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u424
  · exact u425
  · exact u426
  · exact u427

def b1466 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 51 194 84 296 20 169 201 137 393), lower := (rows 51 194 84 296 20 32 64 128 256), losses := [] }

theorem u1466 : Upper (D 0) (R 0) [50,192,80,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1466
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1467 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 51 194 84 296 24 165 197 133 389), lower := (rows 51 194 84 296 24 32 64 128 256), losses := [] }

theorem u1467 : Upper (D 0) (R 0) [50,192,80,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1467
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1468 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 84 296 144 45 77 141 269), lower := (rows 51 194 84 296 144 32 64 128 256), losses := [] }

theorem u1468 : Upper (D 0) (R 0) [50,192,80,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1468
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1469 : Route 9 := (fun mask => (mask,id))

def c1469 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1469 : Upper (D 0) (R 0) [50,192,80,384,1] 13 := by
  apply FastRouting.sound _ _ [50,192,80,384,1] 13 (by decide) (choices 1) [1,4,8] r1469 c1469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u428
  · exact u429
  · exact u430

def b1470 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 51 194 84 392 20 41 105 169 297), lower := (rows 51 194 84 392 20 32 64 128 256), losses := [] }

theorem u1470 : Upper (D 0) (R 0) [50,192,80,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1470
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1471 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 51 194 84 392 24 37 101 165 293), lower := (rows 51 194 84 392 24 32 64 128 256), losses := [] }

theorem u1471 : Upper (D 0) (R 0) [50,192,80,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1471
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1472 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 84 392 48 45 77 141 269), lower := (rows 51 194 84 392 48 32 64 128 256), losses := [] }

theorem u1472 : Upper (D 0) (R 0) [50,192,80,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1472
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1473 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 28 104 17 228 196 196 452), lower := (rows 51 259 28 104 17 32 64 128 256), losses := [] }

theorem u1473 : Upper (D 0) (R 0) [50,257,24,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1473
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1474 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 51 259 28 104 20 225 193 193 449), lower := (rows 51 259 28 104 20 32 64 128 256), losses := [] }

theorem u1474 : Upper (D 0) (R 0) [50,257,24,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1474
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1475 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 28 104 80 165 197 133 389), lower := (rows 51 259 28 104 80 32 64 128 256), losses := [] }

theorem u1475 : Upper (D 0) (R 0) [50,257,24,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1475
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1476 : Route 9 := (fun mask => (mask,id))

def c1476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1476 : Upper (D 0) (R 0) [50,257,24,96,128] 13 := by
  apply FastRouting.sound _ _ [50,257,24,96,128] 13 (by decide) (choices 1) [1,4,64,128] r1476 c1476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u431
  · exact u432
  · exact u433
  · exact u434

def b1477 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 28 200 17 228 228 228 484), lower := (rows 51 259 28 200 17 32 64 128 256), losses := [] }

theorem u1477 : Upper (D 0) (R 0) [50,257,24,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1477
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1478 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 259 28 200 20 225 225 225 481), lower := (rows 51 259 28 200 20 32 64 128 256), losses := [] }

theorem u1478 : Upper (D 0) (R 0) [50,257,24,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1478
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1479 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 259 28 200 48 229 197 197 453), lower := (rows 51 259 28 200 48 32 64 128 256), losses := [] }

theorem u1479 : Upper (D 0) (R 0) [50,257,24,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1479
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1480 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 28 200 80 165 229 165 421), lower := (rows 51 259 28 200 80 32 64 128 256), losses := [] }

theorem u1480 : Upper (D 0) (R 0) [50,257,24,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1480
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1481 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 76 140 17 240 240 240 496), lower := (rows 51 259 76 140 17 32 64 128 256), losses := [] }

theorem u1481 : Upper (D 0) (R 0) [50,257,72,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1481
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1482 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 51 259 76 140 48 241 209 209 465), lower := (rows 51 259 76 140 48 32 64 128 256), losses := [] }

theorem u1482 : Upper (D 0) (R 0) [50,257,72,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1482
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1483 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 51 259 76 140 80 177 241 177 433), lower := (rows 51 259 76 140 80 32 64 128 256), losses := [] }

theorem u1483 : Upper (D 0) (R 0) [50,257,72,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1483
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1484 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 76 152 17 228 228 228 484), lower := (rows 51 259 76 152 17 32 64 128 256), losses := [] }

theorem u1484 : Upper (D 0) (R 0) [50,257,72,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1484
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1485 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 259 76 152 20 225 225 225 481), lower := (rows 51 259 76 152 20 32 64 128 256), losses := [] }

theorem u1485 : Upper (D 0) (R 0) [50,257,72,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1485
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1486 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 259 76 152 48 229 197 197 453), lower := (rows 51 259 76 152 48 32 64 128 256), losses := [] }

theorem u1486 : Upper (D 0) (R 0) [50,257,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1486
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1487 : Route 9 := (fun mask => (mask,id))

def c1487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1487 : Upper (D 0) (R 0) [50,257,72,144,64] 13 := by
  apply FastRouting.sound _ _ [50,257,72,144,64] 13 (by decide) (choices 1) [1,4,128] r1487 c1487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u435
  · exact u436
  · exact u437

def b1488 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 259 76 152 144 101 101 229 357), lower := (rows 51 259 76 152 144 32 64 128 256), losses := [] }

theorem u1488 : Upper (D 0) (R 0) [50,257,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1488
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1489 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 84 104 17 172 204 140 396), lower := (rows 51 259 84 104 17 32 64 128 256), losses := [] }

theorem u1489 : Upper (D 0) (R 0) [50,257,80,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1489
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1490 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 51 259 84 104 20 169 201 137 393), lower := (rows 51 259 84 104 20 32 64 128 256), losses := [] }

theorem u1490 : Upper (D 0) (R 0) [50,257,80,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1490
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1491 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 51 259 84 104 24 165 197 133 389), lower := (rows 51 259 84 104 24 32 64 128 256), losses := [] }

theorem u1491 : Upper (D 0) (R 0) [50,257,80,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1491
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1492_1 : Upper (D 0) (R 0) [50,257,80,96,128,1] 13 :=
  permutation_upper _ _ _ [50,257,80,96,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u438

theorem m1492_4 : Upper (D 0) (R 0) [50,257,80,96,128,4] 13 :=
  permutation_upper _ _ _ [50,257,80,96,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u440

theorem m1492_8 : Upper (D 0) (R 0) [50,257,80,96,128,8] 13 :=
  permutation_upper _ _ _ [50,257,80,96,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u439

def r1492 : Route 9 := (fun mask => (mask,id))

def c1492 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1492 : Upper (D 0) (R 0) [50,257,80,96,128] 13 := by
  apply FastRouting.sound _ _ [50,257,80,96,128] 13 (by decide) (choices 1) [1,4,8,128] r1492 c1492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m1492_1
  · exact m1492_4
  · exact m1492_8
  · exact u441

def b1493 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 84 168 17 236 204 204 460), lower := (rows 51 259 84 168 17 32 64 128 256), losses := [] }

theorem u1493 : Upper (D 0) (R 0) [50,257,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1493
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1494 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 51 259 84 168 20 233 201 201 457), lower := (rows 51 259 84 168 20 32 64 128 256), losses := [] }

theorem u1494 : Upper (D 0) (R 0) [50,257,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1494
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1495 : PairBound 9 := { available := 197, camps := [], pairs := [], upper := (rows 51 259 84 168 24 229 197 197 453), lower := (rows 51 259 84 168 24 32 64 128 256), losses := [] }

theorem u1495 : Upper (D 0) (R 0) [50,257,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1495
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1496 : PairBound 9 := { available := 141, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 51 259 84 168 80 173 205 141 397), lower := (rows 51 259 84 168 80 32 64 128 256), losses := [] }

theorem u1496 : Upper (D 0) (R 0) [50,257,80,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1496
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1497_1 : Upper (D 0) (R 0) [50,257,80,160,128,1] 13 :=
  permutation_upper _ _ _ [50,257,80,160,1,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u442

theorem m1497_4 : Upper (D 0) (R 0) [50,257,80,160,128,4] 13 :=
  permutation_upper _ _ _ [50,257,80,160,8,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u444

theorem m1497_8 : Upper (D 0) (R 0) [50,257,80,160,128,8] 13 :=
  permutation_upper _ _ _ [50,257,80,160,4,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u443

def r1497 : Route 9 := (fun mask => (mask,id))

def c1497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1497 : Upper (D 0) (R 0) [50,257,80,160,128] 13 := by
  apply FastRouting.sound _ _ [50,257,80,160,128] 13 (by decide) (choices 1) [1,4,8,64] r1497 c1497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m1497_1
  · exact m1497_4
  · exact m1497_8
  · exact u445

def b1498 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 84 200 17 172 236 172 428), lower := (rows 51 259 84 200 17 32 64 128 256), losses := [] }

theorem u1498 : Upper (D 0) (R 0) [50,257,80,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1498
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1499 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 51 259 84 200 20 169 233 169 425), lower := (rows 51 259 84 200 20 32 64 128 256), losses := [] }

theorem u1499 : Upper (D 0) (R 0) [50,257,80,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1499
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u1499
end Delivery.IrregularNine14.P00
