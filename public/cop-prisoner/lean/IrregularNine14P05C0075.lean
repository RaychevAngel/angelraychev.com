import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0026
import IrregularNine14P05C0027

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4500 : PairBound 9 := { available := 44, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 280 22 33 108 172 300), lower := (rows 35 67 140 280 22 33 64 128 256), losses := [] }

theorem u4500 : Upper (D 5) (R 5) [34,65,136,272,6,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4500
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4501 : Route 9 := (fun mask => (mask,id))

def c4501 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4501 : Upper (D 5) (R 5) [34,65,136,272,6,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,6,4] 13 (by decide) (choices 1) [1,8,32] r4501 c4501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1613
  · exact u1614
  · exact u1615

def r4502 : Route 9 := (fun mask => (mask,id))

def c4502 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4502 : Upper (D 5) (R 5) [34,65,136,272,6,8] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,6,8] 13 (by decide) (choices 1) [1,4,32] r4502 c4502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1616
  · exact u1617
  · exact u1618

def b4503 : PairBound 9 := { available := 14, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 280 52 33 78 142 270), lower := (rows 35 67 140 280 52 33 64 128 256), losses := [] }

theorem u4503 : Upper (D 5) (R 5) [34,65,136,272,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4503
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4504 : PairBound 9 := { available := 13, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 280 52 34 77 141 269), lower := (rows 35 67 140 280 52 34 64 128 256), losses := [] }

theorem u4504 : Upper (D 5) (R 5) [34,65,136,272,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4504
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4505 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 140 280 52 36 75 139 267), lower := (rows 35 67 140 280 52 36 64 128 256), losses := [] }

theorem u4505 : Upper (D 5) (R 5) [34,65,136,272,36,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4505
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4506 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 140 280 52 40 71 135 263), lower := (rows 35 67 140 280 52 40 64 128 256), losses := [] }

theorem u4506 : Upper (D 5) (R 5) [34,65,136,272,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4506
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4507 : PairBound 9 := { available := 28, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 296 21 34 92 156 284), lower := (rows 35 67 140 296 21 34 64 128 256), losses := [] }

theorem u4507 : Upper (D 5) (R 5) [34,65,136,288,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4507
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4508 : Route 9 := (fun mask => (mask,id))

def c4508 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4508 : Upper (D 5) (R 5) [34,65,136,288,5,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,5,4] 13 (by decide) (choices 1) [2,8,16] r4508 c4508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1619
  · exact u1620
  · exact u1621

def b4509 : PairBound 9 := { available := 22, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 140 296 21 40 86 150 278), lower := (rows 35 67 140 296 21 40 64 128 256), losses := [] }

theorem u4509 : Upper (D 5) (R 5) [34,65,136,288,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4509
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4510 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 396, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 140 296 21 48 78 142 270), lower := (rows 35 67 140 296 21 48 64 128 256), losses := [] }

theorem u4510 : Upper (D 5) (R 5) [34,65,136,288,5,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4510
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4511 : PairBound 9 := { available := 28, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 296 22 33 92 156 284), lower := (rows 35 67 140 296 22 33 64 128 256), losses := [] }

theorem u4511 : Upper (D 5) (R 5) [34,65,136,288,6,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4511
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4512 : Route 9 := (fun mask => (mask,id))

def c4512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4512 : Upper (D 5) (R 5) [34,65,136,288,6,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,6,4] 13 (by decide) (choices 1) [1,8,16] r4512 c4512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1622
  · exact u1623
  · exact u1624

def b4513 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 140 296 22 40 85 149 277), lower := (rows 35 67 140 296 22 40 64 128 256), losses := [] }

theorem u4513 : Upper (D 5) (R 5) [34,65,136,288,6,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4513
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4514 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 140 296 22 48 77 141 269), lower := (rows 35 67 140 296 22 48 64 128 256), losses := [] }

theorem u4514 : Upper (D 5) (R 5) [34,65,136,288,6,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4514
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4515 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 296 26 33 84 148 276), lower := (rows 35 67 140 296 26 33 64 128 256), losses := [] }

theorem u4515 : Upper (D 5) (R 5) [34,65,136,288,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4515
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4516 : Route 9 := (fun mask => (mask,id))

def c4516 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4516 : Upper (D 5) (R 5) [34,65,136,288,10,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,10,4] 13 (by decide) (choices 1) [1,4,16] r4516 c4516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1625
  · exact u1626
  · exact u1627

def b4517 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 140 296 26 48 69 133 261), lower := (rows 35 67 140 296 26 48 64 128 256), losses := [] }

theorem u4517 : Upper (D 5) (R 5) [34,65,136,288,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4517
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4518 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 148 296 21 34 76 140 268), lower := (rows 35 67 148 296 21 34 64 128 256), losses := [] }

theorem u4518 : Upper (D 5) (R 5) [34,65,144,288,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4518
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4519 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 148 296 21 36 74 138 266), lower := (rows 35 67 148 296 21 36 64 128 256), losses := [] }

theorem u4519 : Upper (D 5) (R 5) [34,65,144,288,5,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4519
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4520 : PairBound 9 := { available := 14, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 148 296 21 40 78 142 270), lower := (rows 35 67 148 296 21 40 64 128 256), losses := [] }

theorem u4520 : Upper (D 5) (R 5) [34,65,144,288,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4520
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4521 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 148 296 22 33 76 140 268), lower := (rows 35 67 148 296 22 33 64 128 256), losses := [] }

theorem u4521 : Upper (D 5) (R 5) [34,65,144,288,6,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4521
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4522 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 148 296 22 36 73 137 265), lower := (rows 35 67 148 296 22 36 64 128 256), losses := [] }

theorem u4522 : Upper (D 5) (R 5) [34,65,144,288,6,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4522
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4523 : PairBound 9 := { available := 13, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 148 296 22 40 77 141 269), lower := (rows 35 67 148 296 22 40 64 128 256), losses := [] }

theorem u4523 : Upper (D 5) (R 5) [34,65,144,288,6,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4523
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4524 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 148 296 26 33 76 140 268), lower := (rows 35 67 148 296 26 33 64 128 256), losses := [] }

theorem u4524 : Upper (D 5) (R 5) [34,65,144,288,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4524
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4525 : Route 9 := (fun mask => (mask,id))

def c4525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4525 : Upper (D 5) (R 5) [34,65,144,288,10,4] 13 := by
  apply FastRouting.sound _ _ [34,65,144,288,10,4] 13 (by decide) (choices 1) [1,4,8] r4525 c4525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1628
  · exact u1629
  · exact u1630

def b4526 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 148 296 26 40 69 133 261), lower := (rows 35 67 148 296 26 40 64 128 256), losses := [] }

theorem u4526 : Upper (D 5) (R 5) [34,65,144,288,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4526
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4527 : PairBound 9 := { available := 14, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 148 296 28 33 78 142 270), lower := (rows 35 67 148 296 28 33 64 128 256), losses := [] }

theorem u4527 : Upper (D 5) (R 5) [34,65,144,288,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4527
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4528 : PairBound 9 := { available := 13, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 148 296 28 34 77 141 269), lower := (rows 35 67 148 296 28 34 64 128 256), losses := [] }

theorem u4528 : Upper (D 5) (R 5) [34,65,144,288,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4528
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4529 : PairBound 9 := { available := 11, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 148 296 28 36 75 139 267), lower := (rows 35 67 148 296 28 36 64 128 256), losses := [] }

theorem u4529 : Upper (D 5) (R 5) [34,65,144,288,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4529
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4530 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 148 296 28 40 71 135 263), lower := (rows 35 67 148 296 28 40 64 128 256), losses := [] }

theorem u4530 : Upper (D 5) (R 5) [34,65,144,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4530
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4531 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 338, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 44 137 26 33 340 404 276), lower := (rows 35 70 44 137 26 33 64 128 256), losses := [] }

theorem u4531 : Upper (D 5) (R 5) [34,68,40,129,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4531
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4532 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 44 137 26 48 325 389 261), lower := (rows 35 70 44 137 26 48 64 128 256), losses := [] }

theorem u4532 : Upper (D 5) (R 5) [34,68,40,129,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4532
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4533 : Route 9 := (fun mask => (mask,id))

def c4533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4533 : Upper (D 5) (R 5) [34,68,40,129,10,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,10,256] 13 (by decide) (choices 1) [1,4,16] r4533 c4533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1631
  · exact u1632
  · exact u1633

def b4534 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 44 137 273 34 92 156 284), lower := (rows 35 70 44 137 273 34 64 128 256), losses := [] }

theorem u4534 : Upper (D 5) (R 5) [34,68,40,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4534
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4535 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 408, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 44 137 273 36 90 154 282), lower := (rows 35 70 44 137 273 36 64 128 256), losses := [] }

theorem u4535 : Upper (D 5) (R 5) [34,68,40,129,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4535
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4536 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 44 137 273 40 86 150 278), lower := (rows 35 70 44 137 273 40 64 128 256), losses := [] }

theorem u4536 : Upper (D 5) (R 5) [34,68,40,129,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4536
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4537 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 44 137 273 48 78 142 270), lower := (rows 35 70 44 137 273 48 64 128 256), losses := [] }

theorem u4537 : Upper (D 5) (R 5) [34,68,40,129,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4537
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4538 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 338, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 44 137 274 33 92 156 284), lower := (rows 35 70 44 137 274 33 64 128 256), losses := [] }

theorem u4538 : Upper (D 5) (R 5) [34,68,40,129,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4538
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4539 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 44 137 274 36 89 153 281), lower := (rows 35 70 44 137 274 36 64 128 256), losses := [] }

theorem u4539 : Upper (D 5) (R 5) [34,68,40,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4539
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4540 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 44 137 274 40 85 149 277), lower := (rows 35 70 44 137 274 40 64 128 256), losses := [] }

theorem u4540 : Upper (D 5) (R 5) [34,68,40,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4540
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4541 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 44 137 274 48 77 141 269), lower := (rows 35 70 44 137 274 48 64 128 256), losses := [] }

theorem u4541 : Upper (D 5) (R 5) [34,68,40,129,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4541
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4542 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 44 138 25 33 340 404 276), lower := (rows 35 70 44 138 25 33 64 128 256), losses := [] }

theorem u4542 : Upper (D 5) (R 5) [34,68,40,130,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4542
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4543 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 408, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 44 138 25 36 337 401 273), lower := (rows 35 70 44 138 25 36 64 128 256), losses := [] }

theorem u4543 : Upper (D 5) (R 5) [34,68,40,130,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4543
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4544 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 323, targets := 8 }], pairs := [(0,3)], upper := (rows 35 70 44 138 25 48 325 389 261), lower := (rows 35 70 44 138 25 48 64 128 256), losses := [] }

theorem u4544 : Upper (D 5) (R 5) [34,68,40,130,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4544
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4545 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 292, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 44 138 25 288 85 149 277), lower := (rows 35 70 44 138 25 288 64 128 256), losses := [] }

theorem u4545 : Upper (D 5) (R 5) [34,68,40,130,9,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4545
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4546 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 44 138 273 33 92 156 284), lower := (rows 35 70 44 138 273 33 64 128 256), losses := [] }

theorem u4546 : Upper (D 5) (R 5) [34,68,40,130,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4546
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4547 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 44 138 273 36 89 153 281), lower := (rows 35 70 44 138 273 36 64 128 256), losses := [] }

theorem u4547 : Upper (D 5) (R 5) [34,68,40,130,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4547
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4548 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 44 138 273 40 85 149 277), lower := (rows 35 70 44 138 273 40 64 128 256), losses := [] }

theorem u4548 : Upper (D 5) (R 5) [34,68,40,130,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4548
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4549 : Route 9 := (fun mask => (mask,id))

def c4549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4549 : Upper (D 5) (R 5) [34,68,40,130,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,257,16] 13 (by decide) (choices 1) [1,4,8] r4549 c4549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1634
  · exact u1635
  · exact u1636

def b4550 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 44 138 276 33 89 153 281), lower := (rows 35 70 44 138 276 33 64 128 256), losses := [] }

theorem u4550 : Upper (D 5) (R 5) [34,68,40,130,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4550
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4551 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 44 138 276 40 81 145 273), lower := (rows 35 70 44 138 276 40 64 128 256), losses := [] }

theorem u4551 : Upper (D 5) (R 5) [34,68,40,130,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4551
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4552 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 4 }], pairs := [(3,2)], upper := (rows 35 70 44 138 276 48 73 137 265), lower := (rows 35 70 44 138 276 48 64 128 256), losses := [] }

theorem u4552 : Upper (D 5) (R 5) [34,68,40,130,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4552
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4553 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 44 138 280 33 85 149 277), lower := (rows 35 70 44 138 280 33 64 128 256), losses := [] }

theorem u4553 : Upper (D 5) (R 5) [34,68,40,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4553
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4554 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 44 138 280 36 81 145 273), lower := (rows 35 70 44 138 280 36 64 128 256), losses := [] }

theorem u4554 : Upper (D 5) (R 5) [34,68,40,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4554
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4555 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 35 70 44 138 280 48 69 133 261), lower := (rows 35 70 44 138 280 48 64 128 256), losses := [] }

theorem u4555 : Upper (D 5) (R 5) [34,68,40,130,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4555
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4556 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 44 152 273 33 78 142 270), lower := (rows 35 70 44 152 273 33 64 128 256), losses := [] }

theorem u4556 : Upper (D 5) (R 5) [34,68,40,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4556
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4557 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 44 152 273 34 77 141 269), lower := (rows 35 70 44 152 273 34 64 128 256), losses := [] }

theorem u4557 : Upper (D 5) (R 5) [34,68,40,144,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4557
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4558 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 408, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 44 152 273 36 75 139 267), lower := (rows 35 70 44 152 273 36 64 128 256), losses := [] }

theorem u4558 : Upper (D 5) (R 5) [34,68,40,144,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4558
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4559 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 44 152 273 40 71 135 263), lower := (rows 35 70 44 152 273 40 64 128 256), losses := [] }

theorem u4559 : Upper (D 5) (R 5) [34,68,40,144,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4559
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u4559
end Delivery.IrregularNine14.P05
