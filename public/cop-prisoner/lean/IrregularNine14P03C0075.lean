import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0027

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4500 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 104 152 177 209 145 401), lower := (rows 97 7 262 104 152 32 64 128 256), losses := [] }

theorem u4500 : Upper (D 3) (R 3) [96,5,258,96,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4500
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4501 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 262 137 145 120 120 248 376), lower := (rows 97 7 262 137 145 32 64 128 256), losses := [] }

theorem u4501 : Upper (D 3) (R 3) [96,5,258,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4501
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4502 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 262 137 152 113 113 241 369), lower := (rows 97 7 262 137 152 32 64 128 256), losses := [] }

theorem u4502 : Upper (D 3) (R 3) [96,5,258,129,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4502
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4503 : Route 9 := (fun mask => (mask,id))

def c4503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4503 : Upper (D 3) (R 3) [96,5,258,129,160] 13 := by
  apply FastRouting.sound _ _ [96,5,258,129,160] 13 (by decide) (choices 1) [1,8,16,64] r4503 c4503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1661
  · exact u1662
  · exact u1663
  · exact u1664

def b4504 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 152 152 97 97 225 353), lower := (rows 97 7 262 152 152 32 64 128 256), losses := [] }

theorem u4504 : Upper (D 3) (R 3) [96,5,258,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4504
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4505 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 262 152 176 105 73 201 329), lower := (rows 97 7 262 152 176 32 64 128 256), losses := [] }

theorem u4505 : Upper (D 3) (R 3) [96,5,258,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4505
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4506 : Route 9 := (fun mask => (mask,id))

def c4506 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4506 : Upper (D 3) (R 3) [96,5,258,160,192] 13 := by
  apply FastRouting.sound _ _ [96,5,258,160,192] 13 (by decide) (choices 1) [1,8,16] r4506 c4506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1665
  · exact u1666
  · exact u1667

def b4507 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 268 26 49 225 193 193 449), lower := (rows 97 7 268 26 49 32 64 128 256), losses := [] }

theorem u4507 : Upper (D 3) (R 3) [96,5,264,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4507
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4508 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 26 112 161 193 129 385), lower := (rows 97 7 268 26 112 32 64 128 256), losses := [] }

theorem u4508 : Upper (D 3) (R 3) [96,5,264,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4508
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4509 : Route 9 := (fun mask => (mask,id))

def c4509 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4509 : Upper (D 3) (R 3) [96,5,264,18,129] 13 := by
  apply FastRouting.sound _ _ [96,5,264,18,129] 13 (by decide) (choices 1) [1,64,128] r4509 c4509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1668
  · exact u1669
  · exact u1670

def b4510 : PairBound 9 := { available := 193, camps := [], pairs := [(2,5)], upper := (rows 97 7 268 26 176 225 193 193 449), lower := (rows 97 7 268 26 176 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 67 131 259), good := (rows 449 455 268 478 144 0 64 128 256) }] }

theorem u4510 : Upper (D 3) (R 3) [96,5,264,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4510
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4511 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 268 41 82 177 209 145 401), lower := (rows 97 7 268 41 82 32 64 128 256), losses := [] }

theorem u4511 : Upper (D 3) (R 3) [96,5,264,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4511
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4512 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 268 41 145 242 210 210 466), lower := (rows 97 7 268 41 145 32 64 128 256), losses := [] }

theorem u4512 : Upper (D 3) (R 3) [96,5,264,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4512
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4513 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 268 41 146 241 209 209 465), lower := (rows 97 7 268 41 146 32 64 128 256), losses := [] }

theorem u4513 : Upper (D 3) (R 3) [96,5,264,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4513
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4514 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 268 41 208 179 211 147 403), lower := (rows 97 7 268 41 208 32 64 128 256), losses := [] }

theorem u4514 : Upper (D 3) (R 3) [96,5,264,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4514
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4515 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 268 42 145 241 209 209 465), lower := (rows 97 7 268 42 145 32 64 128 256), losses := [] }

theorem u4515 : Upper (D 3) (R 3) [96,5,264,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4515
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4516 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 268 42 208 177 209 145 401), lower := (rows 97 7 268 42 208 32 64 128 256), losses := [] }

theorem u4516 : Upper (D 3) (R 3) [96,5,264,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4516
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4517 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 268 56 82 161 193 129 385), lower := (rows 97 7 268 56 82 32 64 128 256), losses := [] }

theorem u4517 : Upper (D 3) (R 3) [96,5,264,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4517
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4518 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 268 56 145 227 195 195 451), lower := (rows 97 7 268 56 145 32 64 128 256), losses := [] }

theorem u4518 : Upper (D 3) (R 3) [96,5,264,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4518
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4519 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 268 56 146 225 193 193 449), lower := (rows 97 7 268 56 146 32 64 128 256), losses := [] }

theorem u4519 : Upper (D 3) (R 3) [96,5,264,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4519
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4520 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 268 56 208 163 195 131 387), lower := (rows 97 7 268 56 208 32 64 128 256), losses := [] }

theorem u4520 : Upper (D 3) (R 3) [96,5,264,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4520
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4521 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 268 104 145 179 211 147 403), lower := (rows 97 7 268 104 145 32 64 128 256), losses := [] }

theorem u4521 : Upper (D 3) (R 3) [96,5,264,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4521
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4522 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 268 104 146 177 209 145 401), lower := (rows 97 7 268 104 146 32 64 128 256), losses := [] }

theorem u4522 : Upper (D 3) (R 3) [96,5,264,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4522
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4523 : PairBound 9 := { available := 210, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 268 137 49 242 210 210 466), lower := (rows 97 7 268 137 49 32 64 128 256), losses := [] }

theorem u4523 : Upper (D 3) (R 3) [96,5,264,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4523
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4524 : Route 9 := (fun mask => (mask,id))

def c4524 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4524 : Upper (D 3) (R 3) [96,5,264,129,34] 13 := by
  apply FastRouting.sound _ _ [96,5,264,129,34] 13 (by decide) (choices 1) [1,16,64,128] r4524 c4524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1671
  · exact u1672
  · exact u1673
  · exact u1674

def b4525 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 137 112 179 211 147 403), lower := (rows 97 7 268 137 112 32 64 128 256), losses := [] }

theorem u4525 : Upper (D 3) (R 3) [96,5,264,129,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4525
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4526 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 268 137 145 114 114 242 370), lower := (rows 97 7 268 137 145 32 64 128 256), losses := [] }

theorem u4526 : Upper (D 3) (R 3) [96,5,264,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4526
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4527 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 137 146 113 113 241 369), lower := (rows 97 7 268 137 146 32 64 128 256), losses := [] }

theorem u4527 : Upper (D 3) (R 3) [96,5,264,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4527
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4528 : Route 9 := (fun mask => (mask,id))

def c4528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4528 : Upper (D 3) (R 3) [96,5,264,129,160] 13 := by
  apply FastRouting.sound _ _ [96,5,264,129,160] 13 (by decide) (choices 1) [1,2,16,64] r4528 c4528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1675
  · exact u1676
  · exact u1677
  · exact u1678

def b4529 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 268 138 49 241 209 209 465), lower := (rows 97 7 268 138 49 32 64 128 256), losses := [] }

theorem u4529 : Upper (D 3) (R 3) [96,5,264,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4529
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4530 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 138 112 177 209 145 401), lower := (rows 97 7 268 138 112 32 64 128 256), losses := [] }

theorem u4530 : Upper (D 3) (R 3) [96,5,264,130,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4530
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4531 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 138 145 113 113 241 369), lower := (rows 97 7 268 138 145 32 64 128 256), losses := [] }

theorem u4531 : Upper (D 3) (R 3) [96,5,264,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4531
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4532 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 138 176 113 81 209 337), lower := (rows 97 7 268 138 176 32 64 128 256), losses := [] }

theorem u4532 : Upper (D 3) (R 3) [96,5,264,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4532
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4533 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 268 152 49 227 195 195 451), lower := (rows 97 7 268 152 49 32 64 128 256), losses := [] }

theorem u4533 : Upper (D 3) (R 3) [96,5,264,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4533
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4534 : PairBound 9 := { available := 193, camps := [], pairs := [(2,5)], upper := (rows 97 7 268 152 50 225 193 193 449), lower := (rows 97 7 268 152 50 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 67 131 259), good := (rows 449 455 268 156 478 0 64 128 256) }] }

theorem u4534 : Upper (D 3) (R 3) [96,5,264,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4534
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4535 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 152 112 163 195 131 387), lower := (rows 97 7 268 152 112 32 64 128 256), losses := [] }

theorem u4535 : Upper (D 3) (R 3) [96,5,264,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4535
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4536 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 152 145 99 99 227 355), lower := (rows 97 7 268 152 145 32 64 128 256), losses := [] }

theorem u4536 : Upper (D 3) (R 3) [96,5,264,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4536
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4537 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 152 146 97 97 225 353), lower := (rows 97 7 268 152 146 32 64 128 256), losses := [] }

theorem u4537 : Upper (D 3) (R 3) [96,5,264,144,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4537
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4538 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 152 176 99 67 195 323), lower := (rows 97 7 268 152 176 32 64 128 256), losses := [] }

theorem u4538 : Upper (D 3) (R 3) [96,5,264,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4538
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4539 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 268 168 82 177 209 145 401), lower := (rows 97 7 268 168 82 32 64 128 256), losses := [] }

theorem u4539 : Upper (D 3) (R 3) [96,5,264,160,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4539
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4540 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 268 168 145 115 83 211 339), lower := (rows 97 7 268 168 145 32 64 128 256), losses := [] }

theorem u4540 : Upper (D 3) (R 3) [96,5,264,160,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4540
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4541 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 268 168 146 113 81 209 337), lower := (rows 97 7 268 168 146 32 64 128 256), losses := [] }

theorem u4541 : Upper (D 3) (R 3) [96,5,264,160,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4541
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4542 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 268 168 208 51 83 147 275), lower := (rows 97 7 268 168 208 32 64 128 256), losses := [] }

theorem u4542 : Upper (D 3) (R 3) [96,5,264,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4542
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4543 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 292 26 145 233 201 201 457), lower := (rows 97 7 292 26 145 32 64 128 256), losses := [] }

theorem u4543 : Upper (D 3) (R 3) [96,5,288,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4543
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4544 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 292 26 152 225 193 193 449), lower := (rows 97 7 292 26 152 32 64 128 256), losses := [] }

theorem u4544 : Upper (D 3) (R 3) [96,5,288,18,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4544
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4545 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 292 26 208 169 201 137 393), lower := (rows 97 7 292 26 208 32 64 128 256), losses := [] }

theorem u4545 : Upper (D 3) (R 3) [96,5,288,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4545
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4546 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 292 74 145 185 217 153 409), lower := (rows 97 7 292 74 145 32 64 128 256), losses := [] }

theorem u4546 : Upper (D 3) (R 3) [96,5,288,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4546
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4547 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 292 74 152 177 209 145 401), lower := (rows 97 7 292 74 152 32 64 128 256), losses := [] }

theorem u4547 : Upper (D 3) (R 3) [96,5,288,66,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4547
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4548 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 292 88 145 171 203 139 395), lower := (rows 97 7 292 88 145 32 64 128 256), losses := [] }

theorem u4548 : Upper (D 3) (R 3) [96,5,288,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4548
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4549 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 292 88 146 169 201 137 393), lower := (rows 97 7 292 88 146 32 64 128 256), losses := [] }

theorem u4549 : Upper (D 3) (R 3) [96,5,288,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4549
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4550 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 292 137 146 121 89 217 345), lower := (rows 97 7 292 137 146 32 64 128 256), losses := [] }

theorem u4550 : Upper (D 3) (R 3) [96,5,288,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4550
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4551 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 292 137 208 59 91 155 283), lower := (rows 97 7 292 137 208 32 64 128 256), losses := [] }

theorem u4551 : Upper (D 3) (R 3) [96,5,288,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4551
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4552 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 292 138 208 57 89 153 281), lower := (rows 97 7 292 138 208 32 64 128 256), losses := [] }

theorem u4552 : Upper (D 3) (R 3) [96,5,288,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4552
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4553 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 388 26 49 233 201 201 457), lower := (rows 97 7 388 26 49 32 64 128 256), losses := [] }

theorem u4553 : Upper (D 3) (R 3) [96,5,384,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4553
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4554 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 388 26 56 225 193 193 449), lower := (rows 97 7 388 26 56 32 64 128 256), losses := [] }

theorem u4554 : Upper (D 3) (R 3) [96,5,384,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4554
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4555 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 388 26 112 169 201 137 393), lower := (rows 97 7 388 26 112 32 64 128 256), losses := [] }

theorem u4555 : Upper (D 3) (R 3) [96,5,384,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4555
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4556 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 26 145 105 105 233 361), lower := (rows 97 7 388 26 145 32 64 128 256), losses := [] }

theorem u4556 : Upper (D 3) (R 3) [96,5,384,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4556
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4557 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 26 152 97 97 225 353), lower := (rows 97 7 388 26 152 32 64 128 256), losses := [] }

theorem u4557 : Upper (D 3) (R 3) [96,5,384,18,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4557
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4558 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 26 176 105 73 201 329), lower := (rows 97 7 388 26 176 32 64 128 256), losses := [] }

theorem u4558 : Upper (D 3) (R 3) [96,5,384,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4558
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4559 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 388 41 82 185 217 153 409), lower := (rows 97 7 388 41 82 32 64 128 256), losses := [] }

theorem u4559 : Upper (D 3) (R 3) [96,5,384,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4559
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4559
end Delivery.IrregularNine14.P03
