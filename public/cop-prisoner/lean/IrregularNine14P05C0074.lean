import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0026

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4440 : PairBound 9 := { available := 28, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 133 268 56 34 92 156 284), lower := (rows 35 67 133 268 56 34 64 128 256), losses := [] }

theorem u4440 : Upper (D 5) (R 5) [34,65,129,260,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4440
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4441 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 268 56 36 90 154 282), lower := (rows 35 67 133 268 56 36 64 128 256), losses := [] }

theorem u4441 : Upper (D 5) (R 5) [34,65,129,260,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4441
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4442 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 268 56 40 86 150 278), lower := (rows 35 67 133 268 56 40 64 128 256), losses := [] }

theorem u4442 : Upper (D 5) (R 5) [34,65,129,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4442
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4443 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 133 268 56 48 78 142 270), lower := (rows 35 67 133 268 56 48 64 128 256), losses := [] }

theorem u4443 : Upper (D 5) (R 5) [34,65,129,260,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4443
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4444 : PairBound 9 := { available := 44, camps := [], pairs := [(3,0),(4,0)], upper := (rows 35 67 133 280 26 36 108 172 300), lower := (rows 35 67 133 280 26 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 13 19 36 100 164 292), good := (rows 506 90 508 280 26 492 64 128 256) }] }

theorem u4444 : Upper (D 5) (R 5) [34,65,129,272,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4444
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4445 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 133 280 26 40 100 164 292), lower := (rows 35 67 133 280 26 40 64 128 256), losses := [] }

theorem u4445 : Upper (D 5) (R 5) [34,65,129,272,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4445
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4446 : PairBound 9 := { available := 44, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 133 280 28 34 108 172 300), lower := (rows 35 67 133 280 28 34 64 128 256), losses := [] }

theorem u4446 : Upper (D 5) (R 5) [34,65,129,272,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4446
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4447 : PairBound 9 := { available := 42, camps := [], pairs := [(3,0),(4,0)], upper := (rows 35 67 133 280 28 36 106 170 298), lower := (rows 35 67 133 280 28 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 13 52 52 65 129 257), good := (rows 506 458 508 312 60 60 64 128 256) }] }

theorem u4447 : Upper (D 5) (R 5) [34,65,129,272,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4447
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4448 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 133 280 28 40 102 166 294), lower := (rows 35 67 133 280 28 40 64 128 256), losses := [] }

theorem u4448 : Upper (D 5) (R 5) [34,65,129,272,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4448
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4449 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 133 280 52 34 76 140 268), lower := (rows 35 67 133 280 52 34 64 128 256), losses := [] }

theorem u4449 : Upper (D 5) (R 5) [34,65,129,272,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4449
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4450 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 280 52 36 74 138 266), lower := (rows 35 67 133 280 52 36 64 128 256), losses := [] }

theorem u4450 : Upper (D 5) (R 5) [34,65,129,272,36,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4450
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4451 : Route 9 := (fun mask => (mask,id))

def c4451 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4451 : Upper (D 5) (R 5) [34,65,129,272,36,8] 13 := by
  apply FastRouting.sound _ _ [34,65,129,272,36,8] 13 (by decide) (choices 1) [2,4,8] r4451 c4451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1577
  · exact u1578
  · exact u1579

def b4452 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 133 280 56 34 76 140 268), lower := (rows 35 67 133 280 56 34 64 128 256), losses := [] }

theorem u4452 : Upper (D 5) (R 5) [34,65,129,272,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4452
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4453 : Route 9 := (fun mask => (mask,id))

def c4453 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4453 : Upper (D 5) (R 5) [34,65,129,272,40,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,272,40,4] 13 (by decide) (choices 1) [2,4,8] r4453 c4453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1580
  · exact u1581
  · exact u1582

def b4454 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 133 280 56 40 70 134 262), lower := (rows 35 67 133 280 56 40 64 128 256), losses := [] }

theorem u4454 : Upper (D 5) (R 5) [34,65,129,272,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4454
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4455 : PairBound 9 := { available := 28, camps := [], pairs := [(3,0),(4,0)], upper := (rows 35 67 133 296 26 36 92 156 284), lower := (rows 35 67 133 296 26 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 44 17 36 68 132 260), good := (rows 58 82 508 296 26 492 64 128 256) }] }

theorem u4455 : Upper (D 5) (R 5) [34,65,129,288,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4455
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4456 : PairBound 9 := { available := 20, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 133 296 26 40 84 148 276), lower := (rows 35 67 133 296 26 40 64 128 256), losses := [] }

theorem u4456 : Upper (D 5) (R 5) [34,65,129,288,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4456
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4457 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 133 296 26 48 76 140 268), lower := (rows 35 67 133 296 26 48 64 128 256), losses := [] }

theorem u4457 : Upper (D 5) (R 5) [34,65,129,288,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4457
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4458 : PairBound 9 := { available := 28, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 133 296 28 34 92 156 284), lower := (rows 35 67 133 296 28 34 64 128 256), losses := [] }

theorem u4458 : Upper (D 5) (R 5) [34,65,129,288,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4458
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4459 : PairBound 9 := { available := 26, camps := [], pairs := [(3,0),(4,0)], upper := (rows 35 67 133 296 28 36 90 154 282), lower := (rows 35 67 133 296 28 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 13 52 52 65 129 257), good := (rows 506 458 508 312 60 60 64 128 256) }] }

theorem u4459 : Upper (D 5) (R 5) [34,65,129,288,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4459
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4460 : PairBound 9 := { available := 22, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 133 296 28 40 86 150 278), lower := (rows 35 67 133 296 28 40 64 128 256), losses := [] }

theorem u4460 : Upper (D 5) (R 5) [34,65,129,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4460
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4461 : Route 9 := (fun mask => (mask,id))

def c4461 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4461 : Upper (D 5) (R 5) [34,65,129,288,12,16] 13 := by
  apply FastRouting.sound _ _ [34,65,129,288,12,16] 13 (by decide) (choices 1) [2,4,8] r4461 c4461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1583
  · exact u1584
  · exact u1585

def r4462 : Route 9 := (fun mask => (mask,id))

def c4462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4462 : Upper (D 5) (R 5) [34,65,130,260,9,4] 13 := by
  apply FastRouting.sound _ _ [34,65,130,260,9,4] 13 (by decide) (choices 1) [8,16,32] r4462 c4462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1586
  · exact u1587
  · exact u1588

def r4463 : Route 9 := (fun mask => (mask,id))

def c4463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4463 : Upper (D 5) (R 5) [34,65,130,260,9,8] 13 := by
  apply FastRouting.sound _ _ [34,65,130,260,9,8] 13 (by decide) (choices 1) [4,16,32] r4463 c4463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1589
  · exact u1590
  · exact u1591

def b4464 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 396, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 134 268 25 48 108 172 300), lower := (rows 35 67 134 268 25 48 64 128 256), losses := [] }

theorem u4464 : Upper (D 5) (R 5) [34,65,130,260,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4464
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4465 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 134 268 52 33 88 152 280), lower := (rows 35 67 134 268 52 33 64 128 256), losses := [] }

theorem u4465 : Upper (D 5) (R 5) [34,65,130,260,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4465
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4466 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 134 268 52 40 89 153 281), lower := (rows 35 67 134 268 52 40 64 128 256), losses := [] }

theorem u4466 : Upper (D 5) (R 5) [34,65,130,260,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4466
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4467 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 134 268 52 48 73 137 265), lower := (rows 35 67 134 268 52 48 64 128 256), losses := [] }

theorem u4467 : Upper (D 5) (R 5) [34,65,130,260,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4467
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4468 : PairBound 9 := { available := 28, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 134 268 56 33 92 156 284), lower := (rows 35 67 134 268 56 33 64 128 256), losses := [] }

theorem u4468 : Upper (D 5) (R 5) [34,65,130,260,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4468
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4469 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 134 268 56 36 89 153 281), lower := (rows 35 67 134 268 56 36 64 128 256), losses := [] }

theorem u4469 : Upper (D 5) (R 5) [34,65,130,260,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4469
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4470 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 134 268 56 40 85 149 277), lower := (rows 35 67 134 268 56 40 64 128 256), losses := [] }

theorem u4470 : Upper (D 5) (R 5) [34,65,130,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4470
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4471 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 134 268 56 48 77 141 269), lower := (rows 35 67 134 268 56 48 64 128 256), losses := [] }

theorem u4471 : Upper (D 5) (R 5) [34,65,130,260,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4471
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4472 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 33, targets := 8 }], pairs := [(0,3),(3,1)], upper := (rows 35 67 134 280 25 36 108 172 300), lower := (rows 35 67 134 280 25 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 13 19 36 100 164 292), good := (rows 505 89 508 280 25 492 64 128 256) }] }

theorem u4472 : Upper (D 5) (R 5) [34,65,130,272,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4472
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4473 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 134 280 25 40 100 164 292), lower := (rows 35 67 134 280 25 40 64 128 256), losses := [] }

theorem u4473 : Upper (D 5) (R 5) [34,65,130,272,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4473
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4474 : PairBound 9 := { available := 44, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 134 280 28 33 108 172 300), lower := (rows 35 67 134 280 28 33 64 128 256), losses := [] }

theorem u4474 : Upper (D 5) (R 5) [34,65,130,272,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4474
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4475 : Route 9 := (fun mask => (mask,id))

def c4475 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4475 : Upper (D 5) (R 5) [34,65,130,272,12,4] 13 := by
  apply FastRouting.sound _ _ [34,65,130,272,12,4] 13 (by decide) (choices 1) [1,8,32] r4475 c4475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1592
  · exact u1593
  · exact u1594

def b4476 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 134 280 28 40 101 165 293), lower := (rows 35 67 134 280 28 40 64 128 256), losses := [] }

theorem u4476 : Upper (D 5) (R 5) [34,65,130,272,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4476
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4477 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 134 280 52 33 76 140 268), lower := (rows 35 67 134 280 52 33 64 128 256), losses := [] }

theorem u4477 : Upper (D 5) (R 5) [34,65,130,272,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4477
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4478 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 331, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 134 280 52 36 73 137 265), lower := (rows 35 67 134 280 52 36 64 128 256), losses := [] }

theorem u4478 : Upper (D 5) (R 5) [34,65,130,272,36,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4478
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4479 : Route 9 := (fun mask => (mask,id))

def c4479 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4479 : Upper (D 5) (R 5) [34,65,130,272,36,8] 13 := by
  apply FastRouting.sound _ _ [34,65,130,272,36,8] 13 (by decide) (choices 1) [1,4,8] r4479 c4479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1595
  · exact u1596
  · exact u1597

def b4480 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 134 280 56 33 76 140 268), lower := (rows 35 67 134 280 56 33 64 128 256), losses := [] }

theorem u4480 : Upper (D 5) (R 5) [34,65,130,272,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4480
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4481 : Route 9 := (fun mask => (mask,id))

def c4481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4481 : Upper (D 5) (R 5) [34,65,130,272,40,4] 13 := by
  apply FastRouting.sound _ _ [34,65,130,272,40,4] 13 (by decide) (choices 1) [1,4,8] r4481 c4481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1598
  · exact u1599
  · exact u1600

def b4482 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 134 280 56 40 69 133 261), lower := (rows 35 67 134 280 56 40 64 128 256), losses := [] }

theorem u4482 : Upper (D 5) (R 5) [34,65,130,272,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4482
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4483 : PairBound 9 := { available := 28, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 134 296 28 33 92 156 284), lower := (rows 35 67 134 296 28 33 64 128 256), losses := [] }

theorem u4483 : Upper (D 5) (R 5) [34,65,130,288,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4483
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4484 : Route 9 := (fun mask => (mask,id))

def c4484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4484 : Upper (D 5) (R 5) [34,65,130,288,12,4] 13 := by
  apply FastRouting.sound _ _ [34,65,130,288,12,4] 13 (by decide) (choices 1) [1,8,16] r4484 c4484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1601
  · exact u1602
  · exact u1603

def b4485 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 134 296 28 40 85 149 277), lower := (rows 35 67 134 296 28 40 64 128 256), losses := [] }

theorem u4485 : Upper (D 5) (R 5) [34,65,130,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4485
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4486 : Route 9 := (fun mask => (mask,id))

def c4486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4486 : Upper (D 5) (R 5) [34,65,130,288,12,16] 13 := by
  apply FastRouting.sound _ _ [34,65,130,288,12,16] 13 (by decide) (choices 1) [1,4,8] r4486 c4486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1604
  · exact u1605
  · exact u1606

def b4487 : PairBound 9 := { available := 56, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 268 21 34 120 184 312), lower := (rows 35 67 140 268 21 34 64 128 256), losses := [] }

theorem u4487 : Upper (D 5) (R 5) [34,65,136,260,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4487
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4488 : PairBound 9 := { available := 50, camps := [], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 268 21 40 114 178 306), lower := (rows 35 67 140 268 21 40 64 128 256), losses := [{ target := 2, region := (rows 17 18 0 8 16 44 80 144 272), good := (rows 35 67 168 296 499 40 64 128 256) }] }

theorem u4488 : Upper (D 5) (R 5) [34,65,136,260,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4488
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4489 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 396, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 140 268 21 48 106 170 298), lower := (rows 35 67 140 268 21 48 64 128 256), losses := [] }

theorem u4489 : Upper (D 5) (R 5) [34,65,136,260,5,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4489
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4490 : PairBound 9 := { available := 56, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 268 22 33 120 184 312), lower := (rows 35 67 140 268 22 33 64 128 256), losses := [] }

theorem u4490 : Upper (D 5) (R 5) [34,65,136,260,6,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4490
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4491 : PairBound 9 := { available := 49, camps := [], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 268 22 40 113 177 305), lower := (rows 35 67 140 268 22 40 64 128 256), losses := [{ target := 2, region := (rows 17 18 0 8 16 44 80 144 272), good := (rows 35 67 168 296 499 40 64 128 256) }] }

theorem u4491 : Upper (D 5) (R 5) [34,65,136,260,6,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4491
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4492 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 140 268 22 48 105 169 297), lower := (rows 35 67 140 268 22 48 64 128 256), losses := [] }

theorem u4492 : Upper (D 5) (R 5) [34,65,136,260,6,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4492
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4493 : PairBound 9 := { available := 26, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 268 52 33 90 154 282), lower := (rows 35 67 140 268 52 33 64 128 256), losses := [] }

theorem u4493 : Upper (D 5) (R 5) [34,65,136,260,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4493
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4494 : PairBound 9 := { available := 25, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 268 52 34 89 153 281), lower := (rows 35 67 140 268 52 34 64 128 256), losses := [] }

theorem u4494 : Upper (D 5) (R 5) [34,65,136,260,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4494
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4495 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 67, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 268 52 40 83 147 275), lower := (rows 35 67 140 268 52 40 64 128 256), losses := [] }

theorem u4495 : Upper (D 5) (R 5) [34,65,136,260,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4495
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4496 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 140 268 52 48 75 139 267), lower := (rows 35 67 140 268 52 48 64 128 256), losses := [] }

theorem u4496 : Upper (D 5) (R 5) [34,65,136,260,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4496
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4497 : PairBound 9 := { available := 44, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 280 21 34 108 172 300), lower := (rows 35 67 140 280 21 34 64 128 256), losses := [] }

theorem u4497 : Upper (D 5) (R 5) [34,65,136,272,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4497
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4498 : Route 9 := (fun mask => (mask,id))

def c4498 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4498 : Upper (D 5) (R 5) [34,65,136,272,5,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,5,4] 13 (by decide) (choices 1) [2,8,32] r4498 c4498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1607
  · exact u1608
  · exact u1609

def r4499 : Route 9 := (fun mask => (mask,id))

def c4499 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4499 : Upper (D 5) (R 5) [34,65,136,272,5,8] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,5,8] 13 (by decide) (choices 1) [2,4,32] r4499 c4499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1610
  · exact u1611
  · exact u1612

#print axioms u4499
end Delivery.IrregularNine14.P05
