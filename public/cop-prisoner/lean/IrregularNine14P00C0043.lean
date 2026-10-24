import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0022
import IrregularNine14P00C0023

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2580 : Route 9 := (fun mask => (mask,id))

def c2580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2580 : Upper (D 0) (R 0) [50,68,129,384] 13 := by
  apply FastRouting.sound _ _ [50,68,129,384] 13 (by decide) (choices 1) [1,8,32,64] r2580 c2580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1363
  · exact u1364
  · exact u1365
  · exact u1366

def b2581 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 140 25 497 481 481 481 481), lower := (rows 51 70 140 25 16 32 64 128 256), losses := [] }

theorem u2581 : Upper (D 0) (R 0) [50,68,136,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2581
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2582 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 51 70 140 56 465 481 449 449 449), lower := (rows 51 70 140 56 16 32 64 128 256), losses := [] }

theorem u2582 : Upper (D 0) (R 0) [50,68,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2582
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2583 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 140 73 433 433 497 433 433), lower := (rows 51 70 140 73 16 32 64 128 256), losses := [] }

theorem u2583 : Upper (D 0) (R 0) [50,68,136,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2583
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2584 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 140 88 433 417 481 417 417), lower := (rows 51 70 140 88 16 32 64 128 256), losses := [] }

theorem u2584 : Upper (D 0) (R 0) [50,68,136,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2584
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2585 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 70 140 137 369 369 369 497 369), lower := (rows 51 70 140 137 16 32 64 128 256), losses := [] }

theorem u2585 : Upper (D 0) (R 0) [50,68,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2585
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2586 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 70 140 152 369 353 353 481 353), lower := (rows 51 70 140 152 16 32 64 128 256), losses := [] }

theorem u2586 : Upper (D 0) (R 0) [50,68,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2586
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2587 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 51 70 140 200 305 305 369 433 305), lower := (rows 51 70 140 200 16 32 64 128 256), losses := [] }

theorem u2587 : Upper (D 0) (R 0) [50,68,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2587
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2588 : Route 9 := (fun mask => (mask,id))

def c2588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2588 : Upper (D 0) (R 0) [50,68,136,257] 13 := by
  apply FastRouting.sound _ _ [50,68,136,257] 13 (by decide) (choices 1) [1,32,64,128] r2588 c2588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1367
  · exact u1368
  · exact u1369
  · exact u1370

def r2589 : Route 9 := (fun mask => (mask,id))

def c2589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2589 : Upper (D 0) (R 0) [50,68,136,272] 13 := by
  apply FastRouting.sound _ _ [50,68,136,272] 13 (by decide) (choices 1) [1,32,64,128] r2589 c2589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1371
  · exact u1372
  · exact u1373
  · exact u1374

def b2590 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 140 328 177 177 241 177 433), lower := (rows 51 70 140 328 16 32 64 128 256), losses := [] }

theorem u2590 : Upper (D 0) (R 0) [50,68,136,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2590
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2591 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 70 140 392 113 113 113 241 369), lower := (rows 51 70 140 392 16 32 64 128 256), losses := [] }

theorem u2591 : Upper (D 0) (R 0) [50,68,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2591
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2592 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 261 25 248 232 232 232 488), lower := (rows 51 70 261 25 16 32 64 128 256), losses := [] }

theorem u2592 : Upper (D 0) (R 0) [50,68,257,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2592
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2593 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 51 70 261 56 217 233 201 201 457), lower := (rows 51 70 261 56 16 32 64 128 256), losses := [] }

theorem u2593 : Upper (D 0) (R 0) [50,68,257,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2593
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2594 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 261 73 184 184 248 184 440), lower := (rows 51 70 261 73 16 32 64 128 256), losses := [] }

theorem u2594 : Upper (D 0) (R 0) [50,68,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2594
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2595 : Route 9 := (fun mask => (mask,id))

def c2595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2595 : Upper (D 0) (R 0) [50,68,257,80] 13 := by
  apply FastRouting.sound _ _ [50,68,257,80] 13 (by decide) (choices 1) [1,8,32,128] r2595 c2595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1375
  · exact u1376
  · exact u1377
  · exact u1378

def r2596 : Route 9 := (fun mask => (mask,id))

def c2596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2596 : Upper (D 0) (R 0) [50,68,257,129] 13 := by
  apply FastRouting.sound _ _ [50,68,257,129] 13 (by decide) (choices 1) [8,32,64,128] r2596 c2596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1379
  · exact u1380
  · exact u1381
  · exact u1382

def r2597 : Route 9 := (fun mask => (mask,id))

def c2597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2597 : Upper (D 0) (R 0) [50,68,257,144] 13 := by
  apply FastRouting.sound _ _ [50,68,257,144] 13 (by decide) (choices 1) [1,8,32,64,128] r2597 c2597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1383
  · exact u1384
  · exact u1385
  · exact u1386
  · exact u1387

def r2598 : Route 9 := (fun mask => (mask,id))

def c2598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2598 : Upper (D 0) (R 0) [50,68,257,192] 13 := by
  apply FastRouting.sound _ _ [50,68,257,192] 13 (by decide) (choices 1) [1,8,32,128] r2598 c2598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1388
  · exact u1389
  · exact u1390
  · exact u1391

def b2599 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 268 25 241 225 225 225 481), lower := (rows 51 70 268 25 16 32 64 128 256), losses := [] }

theorem u2599 : Upper (D 0) (R 0) [50,68,264,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2599
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2600 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 51 70 268 56 209 225 193 193 449), lower := (rows 51 70 268 56 16 32 64 128 256), losses := [] }

theorem u2600 : Upper (D 0) (R 0) [50,68,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2600
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2601 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 268 73 177 177 241 177 433), lower := (rows 51 70 268 73 16 32 64 128 256), losses := [] }

theorem u2601 : Upper (D 0) (R 0) [50,68,264,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2601
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2602 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 268 88 177 161 225 161 417), lower := (rows 51 70 268 88 16 32 64 128 256), losses := [] }

theorem u2602 : Upper (D 0) (R 0) [50,68,264,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2602
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2603 : Route 9 := (fun mask => (mask,id))

def c2603 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2603 : Upper (D 0) (R 0) [50,68,264,129] 13 := by
  apply FastRouting.sound _ _ [50,68,264,129] 13 (by decide) (choices 1) [1,32,64,128] r2603 c2603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1392
  · exact u1393
  · exact u1394
  · exact u1395

def r2604 : Route 9 := (fun mask => (mask,id))

def c2604 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2604 : Upper (D 0) (R 0) [50,68,264,144] 13 := by
  apply FastRouting.sound _ _ [50,68,264,144] 13 (by decide) (choices 1) [1,32,64,128] r2604 c2604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1396
  · exact u1397
  · exact u1398
  · exact u1399

def b2605 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 268 200 177 177 241 177 433), lower := (rows 51 70 268 200 16 32 64 128 256), losses := [] }

theorem u2605 : Upper (D 0) (R 0) [50,68,264,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2605
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2606 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 388 25 249 233 233 233 489), lower := (rows 51 70 388 25 16 32 64 128 256), losses := [] }

theorem u2606 : Upper (D 0) (R 0) [50,68,384,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2606
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2607 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 51 70 388 56 217 233 201 201 457), lower := (rows 51 70 388 56 16 32 64 128 256), losses := [] }

theorem u2607 : Upper (D 0) (R 0) [50,68,384,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2607
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2608 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 388 73 185 185 249 185 441), lower := (rows 51 70 388 73 16 32 64 128 256), losses := [] }

theorem u2608 : Upper (D 0) (R 0) [50,68,384,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2608
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2609 : Route 9 := (fun mask => (mask,id))

def c2609 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2609 : Upper (D 0) (R 0) [50,68,384,80] 13 := by
  apply FastRouting.sound _ _ [50,68,384,80] 13 (by decide) (choices 1) [1,8,32,128] r2609 c2609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1400
  · exact u1401
  · exact u1402
  · exact u1403

def r2610 : Route 9 := (fun mask => (mask,id))

def c2610 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2610 : Upper (D 0) (R 0) [50,68,384,129] 13 := by
  apply FastRouting.sound _ _ [50,68,384,129] 13 (by decide) (choices 1) [1,8,32,64] r2610 c2610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1404
  · exact u1405
  · exact u1406
  · exact u1407

def r2611 : Route 9 := (fun mask => (mask,id))

def c2611 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2611 : Upper (D 0) (R 0) [50,68,384,144] 13 := by
  apply FastRouting.sound _ _ [50,68,384,144] 13 (by decide) (choices 1) [1,8,32,64] r2611 c2611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1408
  · exact u1409
  · exact u1410
  · exact u1411

def r2612 : Route 9 := (fun mask => (mask,id))

def c2612 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2612 : Upper (D 0) (R 0) [50,68,384,192] 13 := by
  apply FastRouting.sound _ _ [50,68,384,192] 13 (by decide) (choices 1) [1,8,32] r2612 c2612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1412
  · exact u1413
  · exact u1414

def b2613 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 13 13 496 496 496 496 496), lower := (rows 51 194 13 13 16 32 64 128 256), losses := [] }

theorem u2613 : Upper (D 0) (R 0) [50,192,9,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2613
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2614 : PairBound 9 := { available := 484, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 13 25 500 484 484 484 484), lower := (rows 51 194 13 25 16 32 64 128 256), losses := [] }

theorem u2614 : Upper (D 0) (R 0) [50,192,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2614
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2615 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 13 28 497 481 481 481 481), lower := (rows 51 194 13 28 16 32 64 128 256), losses := [] }

theorem u2615 : Upper (D 0) (R 0) [50,192,9,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2615
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2616 : PairBound 9 := { available := 453, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 13 56 469 485 453 453 453), lower := (rows 51 194 13 56 16 32 64 128 256), losses := [] }

theorem u2616 : Upper (D 0) (R 0) [50,192,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2616
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2617 : PairBound 9 := { available := 436, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 13 73 436 436 500 436 436), lower := (rows 51 194 13 73 16 32 64 128 256), losses := [] }

theorem u2617 : Upper (D 0) (R 0) [50,192,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2617
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2618 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 51 194 13 76 433 433 497 433 433), lower := (rows 51 194 13 76 16 32 64 128 256), losses := [] }

theorem u2618 : Upper (D 0) (R 0) [50,192,9,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2618
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2619 : PairBound 9 := { available := 421, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 13 88 437 421 485 421 421), lower := (rows 51 194 13 88 16 32 64 128 256), losses := [] }

theorem u2619 : Upper (D 0) (R 0) [50,192,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2619
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2620 : PairBound 9 := { available := 309, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 51 194 13 200 309 309 373 437 309), lower := (rows 51 194 13 200 16 32 64 128 256), losses := [] }

theorem u2620 : Upper (D 0) (R 0) [50,192,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2620
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2621 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 13 265 244 244 244 244 500), lower := (rows 51 194 13 265 16 32 64 128 256), losses := [] }

theorem u2621 : Upper (D 0) (R 0) [50,192,9,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2621
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2622 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2622 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2622 : Upper (D 0) (R 0) [50,192,9,260] 13 := by
  apply FastRouting.sound _ _ [50,192,9,260] 13 (by decide) (choices 1) [1,32,64] r2622 c2622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1415
  · exact u1416
  · exact u1417

def b2623 : PairBound 9 := { available := 229, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 13 280 245 229 229 229 485), lower := (rows 51 194 13 280 16 32 64 128 256), losses := [] }

theorem u2623 : Upper (D 0) (R 0) [50,192,9,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2623
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2624 : Route 9 := (fun mask => (mask,id))

def c2624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2624 : Upper (D 0) (R 0) [50,192,9,320] 13 := by
  apply FastRouting.sound _ _ [50,192,9,320] 13 (by decide) (choices 1) [1,4,32,128] r2624 c2624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1418
  · exact u1419
  · exact u1420
  · exact u1421

def b2625 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 21 44 473 489 457 457 457), lower := (rows 51 194 21 44 16 32 64 128 256), losses := [] }

theorem u2625 : Upper (D 0) (R 0) [50,192,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2625
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2626 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 21 76 441 425 489 425 425), lower := (rows 51 194 21 76 16 32 64 128 256), losses := [] }

theorem u2626 : Upper (D 0) (R 0) [50,192,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2626
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2627 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 21 104 413 429 461 397 397), lower := (rows 51 194 21 104 16 32 64 128 256), losses := [] }

theorem u2627 : Upper (D 0) (R 0) [50,192,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2627
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2628 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 21 265 252 236 236 236 492), lower := (rows 51 194 21 265 16 32 64 128 256), losses := [] }

theorem u2628 : Upper (D 0) (R 0) [50,192,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2628
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2629 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 21 268 249 233 233 233 489), lower := (rows 51 194 21 268 16 32 64 128 256), losses := [] }

theorem u2629 : Upper (D 0) (R 0) [50,192,17,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2629
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2630 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 21 296 221 237 205 205 461), lower := (rows 51 194 21 296 16 32 64 128 256), losses := [] }

theorem u2630 : Upper (D 0) (R 0) [50,192,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2630
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2631 : PairBound 9 := { available := 173, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 21 328 189 173 237 173 429), lower := (rows 51 194 21 328 16 32 64 128 256), losses := [] }

theorem u2631 : Upper (D 0) (R 0) [50,192,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2631
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2632 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 28 44 465 481 449 449 449), lower := (rows 51 194 28 44 16 32 64 128 256), losses := [] }

theorem u2632 : Upper (D 0) (R 0) [50,192,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2632
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2633 : PairBound 9 := { available := 421, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 28 73 437 421 485 421 421), lower := (rows 51 194 28 73 16 32 64 128 256), losses := [] }

theorem u2633 : Upper (D 0) (R 0) [50,192,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2633
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2634 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 28 76 433 417 481 417 417), lower := (rows 51 194 28 76 16 32 64 128 256), losses := [] }

theorem u2634 : Upper (D 0) (R 0) [50,192,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2634
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2635 : Route 9 := (fun mask => (mask,id))

def c2635 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 64 => 6 | _ => 0)

theorem u2635 : Upper (D 0) (R 0) [50,192,24,96] 13 := by
  apply FastRouting.sound _ _ [50,192,24,96] 13 (by decide) (choices 1) [1,4,128,256] r2635 c2635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1422
  · exact u1423
  · exact u1424
  · exact u1425

def b2636 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 51 194 28 200 309 293 357 421 293), lower := (rows 51 194 28 200 16 32 64 128 256), losses := [] }

theorem u2636 : Upper (D 0) (R 0) [50,192,24,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2636
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2637 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2637 : Upper (D 0) (R 0) [50,192,24,257] 13 := by
  apply FastRouting.sound _ _ [50,192,24,257] 13 (by decide) (choices 1) [1,4,32,64] r2637 c2637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1426
  · exact u1427
  · exact u1428
  · exact u1429

def b2638 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 28 268 241 225 225 225 481), lower := (rows 51 194 28 268 16 32 64 128 256), losses := [] }

theorem u2638 : Upper (D 0) (R 0) [50,192,24,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2638
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2639 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2639 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2639 : Upper (D 0) (R 0) [50,192,24,288] 13 := by
  apply FastRouting.sound _ _ [50,192,24,288] 13 (by decide) (choices 1) [1,4,64] r2639 c2639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1430
  · exact u1431
  · exact u1432

#print axioms u2639
end Delivery.IrregularNine14.P00
