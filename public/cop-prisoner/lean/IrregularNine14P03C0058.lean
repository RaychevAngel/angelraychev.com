import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0022
import IrregularNine14P03C0023

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3480 : Route 9 := (fun mask => (mask,id))

def c3480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3480 : Upper (D 3) (R 3) [34,68,257,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,257,80,160] 13 (by decide) (choices 1) [1,8,128] r3480 c3480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1367
  · exact u1368
  · exact u1369

def r3481 : Route 9 := (fun mask => (mask,id))

def c3481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3481 : Upper (D 3) (R 3) [34,68,257,96,129] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96,129] 13 (by decide) (choices 1) [1,8,16,128] r3481 c3481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1370
  · exact u1371
  · exact u1372
  · exact u1373

def r3482 : Route 9 := (fun mask => (mask,id))

def c3482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3482 : Upper (D 3) (R 3) [34,68,257,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96,136] 13 (by decide) (choices 1) [1,16,128] r3482 c3482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1374
  · exact u1375
  · exact u1376

def b3483 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 261 137 145 120 120 248 376), lower := (rows 35 70 261 137 145 32 64 128 256), losses := [] }

theorem u3483 : Upper (D 3) (R 3) [34,68,257,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3483
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3484 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 261 137 152 113 113 241 369), lower := (rows 35 70 261 137 152 32 64 128 256), losses := [] }

theorem u3484 : Upper (D 3) (R 3) [34,68,257,129,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3484
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3485 : Route 9 := (fun mask => (mask,id))

def c3485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3485 : Upper (D 3) (R 3) [34,68,257,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,257,129,160] 13 (by decide) (choices 1) [1,8,16,64] r3485 c3485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1377
  · exact u1378
  · exact u1379
  · exact u1380

def r3486 : Route 9 := (fun mask => (mask,id))

def c3486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3486 : Upper (D 3) (R 3) [34,68,257,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,257,129,192] 13 (by decide) (choices 1) [1,8,16] r3486 c3486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1381
  · exact u1382
  · exact u1383

def b3487 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 152 152 97 97 225 353), lower := (rows 35 70 261 152 152 32 64 128 256), losses := [] }

theorem u3487 : Upper (D 3) (R 3) [34,68,257,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3487
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3488 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 261 152 176 105 73 201 329), lower := (rows 35 70 261 152 176 32 64 128 256), losses := [] }

theorem u3488 : Upper (D 3) (R 3) [34,68,257,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3488
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3489 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 261 152 208 41 105 169 297), lower := (rows 35 70 261 152 208 32 64 128 256), losses := [] }

theorem u3489 : Upper (D 3) (R 3) [34,68,257,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3489
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3490 : Route 9 := (fun mask => (mask,id))

def c3490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3490 : Upper (D 3) (R 3) [34,68,257,160,192] 13 := by
  apply FastRouting.sound _ _ [34,68,257,160,192] 13 (by decide) (choices 1) [1,8,16] r3490 c3490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1384
  · exact u1385
  · exact u1386

def b3491 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 268 25 49 225 193 193 449), lower := (rows 35 70 268 25 49 32 64 128 256), losses := [] }

theorem u3491 : Upper (D 3) (R 3) [34,68,264,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3491
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3492 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 268 25 81 161 225 161 417), lower := (rows 35 70 268 25 81 32 64 128 256), losses := [] }

theorem u3492 : Upper (D 3) (R 3) [34,68,264,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3492
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3493 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 268 25 112 161 193 129 385), lower := (rows 35 70 268 25 112 32 64 128 256), losses := [] }

theorem u3493 : Upper (D 3) (R 3) [34,68,264,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3493
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3494 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 268 25 145 225 225 225 481), lower := (rows 35 70 268 25 145 32 64 128 256), losses := [] }

theorem u3494 : Upper (D 3) (R 3) [34,68,264,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3494
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3495 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 268 25 176 225 193 193 449), lower := (rows 35 70 268 25 176 32 64 128 256), losses := [] }

theorem u3495 : Upper (D 3) (R 3) [34,68,264,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3495
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3496 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 25 208 161 225 161 417), lower := (rows 35 70 268 25 208 32 64 128 256), losses := [] }

theorem u3496 : Upper (D 3) (R 3) [34,68,264,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3496
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3497 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 268 137 49 241 209 209 465), lower := (rows 35 70 268 137 49 32 64 128 256), losses := [] }

theorem u3497 : Upper (D 3) (R 3) [34,68,264,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3497
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3498 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 268 137 81 177 241 177 433), lower := (rows 35 70 268 137 81 32 64 128 256), losses := [] }

theorem u3498 : Upper (D 3) (R 3) [34,68,264,129,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3498
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3499 : Route 9 := (fun mask => (mask,id))

def c3499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3499 : Upper (D 3) (R 3) [34,68,264,129,96] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129,96] 13 (by decide) (choices 1) [1,16,128] r3499 c3499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1387
  · exact u1388
  · exact u1389

def b3500 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 268 137 145 113 113 241 369), lower := (rows 35 70 268 137 145 32 64 128 256), losses := [] }

theorem u3500 : Upper (D 3) (R 3) [34,68,264,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3500
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3501 : Route 9 := (fun mask => (mask,id))

def c3501 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3501 : Upper (D 3) (R 3) [34,68,264,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129,160] 13 (by decide) (choices 1) [1,16,64] r3501 c3501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1390
  · exact u1391
  · exact u1392

def r3502 : Route 9 := (fun mask => (mask,id))

def c3502 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3502 : Upper (D 3) (R 3) [34,68,264,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129,192] 13 (by decide) (choices 1) [1,16] r3502 c3502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1393
  · exact u1394

def b3503 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 268 152 49 225 193 193 449), lower := (rows 35 70 268 152 49 32 64 128 256), losses := [] }

theorem u3503 : Upper (D 3) (R 3) [34,68,264,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3503
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3504 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 268 152 81 161 225 161 417), lower := (rows 35 70 268 152 81 32 64 128 256), losses := [] }

theorem u3504 : Upper (D 3) (R 3) [34,68,264,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3504
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3505 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 152 112 161 193 129 385), lower := (rows 35 70 268 152 112 32 64 128 256), losses := [] }

theorem u3505 : Upper (D 3) (R 3) [34,68,264,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3505
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3506 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 268 152 145 97 97 225 353), lower := (rows 35 70 268 152 145 32 64 128 256), losses := [] }

theorem u3506 : Upper (D 3) (R 3) [34,68,264,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3506
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3507 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 268 152 176 97 65 193 321), lower := (rows 35 70 268 152 176 32 64 128 256), losses := [] }

theorem u3507 : Upper (D 3) (R 3) [34,68,264,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3507
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3508 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 268 152 208 33 97 161 289), lower := (rows 35 70 268 152 208 32 64 128 256), losses := [] }

theorem u3508 : Upper (D 3) (R 3) [34,68,264,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3508
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3509 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 388 25 25 225 225 225 481), lower := (rows 35 70 388 25 25 32 64 128 256), losses := [] }

theorem u3509 : Upper (D 3) (R 3) [34,68,384,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3509
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3510 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 25 49 233 201 201 457), lower := (rows 35 70 388 25 49 32 64 128 256), losses := [] }

theorem u3510 : Upper (D 3) (R 3) [34,68,384,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3510
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3511 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 25 56 225 193 193 449), lower := (rows 35 70 388 25 56 32 64 128 256), losses := [] }

theorem u3511 : Upper (D 3) (R 3) [34,68,384,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3511
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3512 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 388 25 81 169 233 169 425), lower := (rows 35 70 388 25 81 32 64 128 256), losses := [] }

theorem u3512 : Upper (D 3) (R 3) [34,68,384,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3512
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3513 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 25 88 161 225 161 417), lower := (rows 35 70 388 25 88 32 64 128 256), losses := [] }

theorem u3513 : Upper (D 3) (R 3) [34,68,384,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3513
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3514 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 388 25 112 169 201 137 393), lower := (rows 35 70 388 25 112 32 64 128 256), losses := [] }

theorem u3514 : Upper (D 3) (R 3) [34,68,384,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3514
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3515 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 388 25 145 105 105 233 361), lower := (rows 35 70 388 25 145 32 64 128 256), losses := [] }

theorem u3515 : Upper (D 3) (R 3) [34,68,384,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3515
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3516 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 388 25 152 97 97 225 353), lower := (rows 35 70 388 25 152 32 64 128 256), losses := [] }

theorem u3516 : Upper (D 3) (R 3) [34,68,384,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3516
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3517 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 388 25 176 105 73 201 329), lower := (rows 35 70 388 25 176 32 64 128 256), losses := [] }

theorem u3517 : Upper (D 3) (R 3) [34,68,384,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3517
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3518 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 25 208 41 105 169 297), lower := (rows 35 70 388 25 208 32 64 128 256), losses := [] }

theorem u3518 : Upper (D 3) (R 3) [34,68,384,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3518
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3519 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 388 41 88 177 209 145 401), lower := (rows 35 70 388 41 88 32 64 128 256), losses := [] }

theorem u3519 : Upper (D 3) (R 3) [34,68,384,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3519
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3520 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 388 41 152 113 81 209 337), lower := (rows 35 70 388 41 152 32 64 128 256), losses := [] }

theorem u3520 : Upper (D 3) (R 3) [34,68,384,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3520
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3521 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 388 41 208 57 89 153 281), lower := (rows 35 70 388 41 208 32 64 128 256), losses := [] }

theorem u3521 : Upper (D 3) (R 3) [34,68,384,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3521
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3522 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 56 81 169 201 137 393), lower := (rows 35 70 388 56 81 32 64 128 256), losses := [] }

theorem u3522 : Upper (D 3) (R 3) [34,68,384,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3522
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3523 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 388 56 88 161 193 129 385), lower := (rows 35 70 388 56 88 32 64 128 256), losses := [] }

theorem u3523 : Upper (D 3) (R 3) [34,68,384,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3523
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3524 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 388 56 145 105 73 201 329), lower := (rows 35 70 388 56 145 32 64 128 256), losses := [] }

theorem u3524 : Upper (D 3) (R 3) [34,68,384,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3524
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3525 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 388 56 152 97 65 193 321), lower := (rows 35 70 388 56 152 32 64 128 256), losses := [] }

theorem u3525 : Upper (D 3) (R 3) [34,68,384,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3525
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3526 : Route 9 := (fun mask => (mask,id))

def c3526 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3526 : Upper (D 3) (R 3) [34,68,384,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,192] 13 (by decide) (choices 1) [1,8] r3526 c3526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1395
  · exact u1396

def b3527 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 73 152 49 113 177 305), lower := (rows 35 70 388 73 152 32 64 128 256), losses := [] }

theorem u3527 : Upper (D 3) (R 3) [34,68,384,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3527
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3528 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 73 176 57 89 153 281), lower := (rows 35 70 388 73 176 32 64 128 256), losses := [] }

theorem u3528 : Upper (D 3) (R 3) [34,68,384,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3528
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3529 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 388 88 145 41 105 169 297), lower := (rows 35 70 388 88 145 32 64 128 256), losses := [] }

theorem u3529 : Upper (D 3) (R 3) [34,68,384,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3529
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3530 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 88 152 33 97 161 289), lower := (rows 35 70 388 88 152 32 64 128 256), losses := [] }

theorem u3530 : Upper (D 3) (R 3) [34,68,384,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3530
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3531 : Route 9 := (fun mask => (mask,id))

def c3531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3531 : Upper (D 3) (R 3) [34,68,384,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80,160] 13 (by decide) (choices 1) [1,8] r3531 c3531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1397
  · exact u1398

def b3532 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 388 104 145 57 89 153 281), lower := (rows 35 70 388 104 145 32 64 128 256), losses := [] }

theorem u3532 : Upper (D 3) (R 3) [34,68,384,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3532
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3533 : Route 9 := (fun mask => (mask,id))

def c3533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3533 : Upper (D 3) (R 3) [34,68,384,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,136] 13 (by decide) (choices 1) [1,16] r3533 c3533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1399
  · exact u1400

def b3534 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 13 112 433 465 401 401), lower := (rows 35 194 13 13 112 32 64 128 256), losses := [] }

theorem u3534 : Upper (D 3) (R 3) [34,192,9,5,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3534
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3535 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 13 273 240 240 240 496), lower := (rows 35 194 13 13 273 32 64 128 256), losses := [] }

theorem u3535 : Upper (D 3) (R 3) [34,192,9,5,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3535
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3536 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 13 304 241 209 209 465), lower := (rows 35 194 13 13 304 32 64 128 256), losses := [] }

theorem u3536 : Upper (D 3) (R 3) [34,192,9,5,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3536
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3537 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 13 336 177 241 177 433), lower := (rows 35 194 13 13 336 32 64 128 256), losses := [] }

theorem u3537 : Upper (D 3) (R 3) [34,192,9,5,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3537
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3538 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 25 52 481 449 449 449), lower := (rows 35 194 13 25 52 32 64 128 256), losses := [] }

theorem u3538 : Upper (D 3) (R 3) [34,192,9,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3538
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3539 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 25 84 417 481 417 417), lower := (rows 35 194 13 25 84 32 64 128 256), losses := [] }

theorem u3539 : Upper (D 3) (R 3) [34,192,9,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3539
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u3539
end Delivery.IrregularNine14.P03
