import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0027
import IrregularNine14P03C0028

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4560 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 388 41 88 179 211 147 403), lower := (rows 97 7 388 41 88 32 64 128 256), losses := [] }

theorem u4560 : Upper (D 3) (R 3) [96,5,384,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4560
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4561 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 388 41 145 122 90 218 346), lower := (rows 97 7 388 41 145 32 64 128 256), losses := [] }

theorem u4561 : Upper (D 3) (R 3) [96,5,384,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4561
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4562 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 388 41 152 115 83 211 339), lower := (rows 97 7 388 41 152 32 64 128 256), losses := [] }

theorem u4562 : Upper (D 3) (R 3) [96,5,384,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4562
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4563 : PairBound 9 := { available := 27, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 388 41 208 59 91 155 283), lower := (rows 97 7 388 41 208 32 64 128 256), losses := [] }

theorem u4563 : Upper (D 3) (R 3) [96,5,384,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4563
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4564 : Route 9 := (fun mask => (mask,id))

def c4564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4564 : Upper (D 3) (R 3) [96,5,384,34,72] 13 := by
  apply FastRouting.sound _ _ [96,5,384,34,72] 13 (by decide) (choices 1) [1,16,128] r4564 c4564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1679
  · exact u1680
  · exact u1681

def r4565 : Route 9 := (fun mask => (mask,id))

def c4565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4565 : Upper (D 3) (R 3) [96,5,384,34,129] 13 := by
  apply FastRouting.sound _ _ [96,5,384,34,129] 13 (by decide) (choices 1) [1,8,16,64] r4565 c4565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1682
  · exact u1683
  · exact u1684
  · exact u1685

def b4566 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 42 152 113 81 209 337), lower := (rows 97 7 388 42 152 32 64 128 256), losses := [] }

theorem u4566 : Upper (D 3) (R 3) [96,5,384,34,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4566
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4567 : Route 9 := (fun mask => (mask,id))

def c4567 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4567 : Upper (D 3) (R 3) [96,5,384,34,192] 13 := by
  apply FastRouting.sound _ _ [96,5,384,34,192] 13 (by decide) (choices 1) [1,8,16] r4567 c4567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1686
  · exact u1687
  · exact u1688

def b4568 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 388 56 88 163 195 131 387), lower := (rows 97 7 388 56 88 32 64 128 256), losses := [] }

theorem u4568 : Upper (D 3) (R 3) [96,5,384,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4568
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4569 : Route 9 := (fun mask => (mask,id))

def c4569 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4569 : Upper (D 3) (R 3) [96,5,384,48,129] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,129] 13 (by decide) (choices 1) [1,2,8,64] r4569 c4569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1689
  · exact u1690
  · exact u1691
  · exact u1692

def b4570 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 56 146 105 73 201 329), lower := (rows 97 7 388 56 146 32 64 128 256), losses := [] }

theorem u4570 : Upper (D 3) (R 3) [96,5,384,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4570
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4571 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 388 56 152 99 67 195 323), lower := (rows 97 7 388 56 152 32 64 128 256), losses := [] }

theorem u4571 : Upper (D 3) (R 3) [96,5,384,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4571
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4572 : Route 9 := (fun mask => (mask,id))

def c4572 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4572 : Upper (D 3) (R 3) [96,5,384,48,192] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,192] 13 (by decide) (choices 1) [1,2,8] r4572 c4572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1693
  · exact u1694
  · exact u1695

def b4573 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 388 104 145 59 91 155 283), lower := (rows 97 7 388 104 145 32 64 128 256), losses := [] }

theorem u4573 : Upper (D 3) (R 3) [96,5,384,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4573
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4574 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 388 104 152 51 83 147 275), lower := (rows 97 7 388 104 152 32 64 128 256), losses := [] }

theorem u4574 : Upper (D 3) (R 3) [96,5,384,96,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4574
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4575 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 22 41 145 481 449 449 449), lower := (rows 97 14 22 41 145 32 64 128 256), losses := [] }

theorem u4575 : Upper (D 3) (R 3) [96,12,18,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4575
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4576 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 22 41 273 225 193 193 449), lower := (rows 97 14 22 41 273 32 64 128 256), losses := [] }

theorem u4576 : Upper (D 3) (R 3) [96,12,18,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4576
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4577 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 22 41 400 225 193 193 449), lower := (rows 97 14 22 41 400 32 64 128 256), losses := [] }

theorem u4577 : Upper (D 3) (R 3) [96,12,18,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4577
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4578 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 22 104 145 417 449 385 385), lower := (rows 97 14 22 104 145 32 64 128 256), losses := [] }

theorem u4578 : Upper (D 3) (R 3) [96,12,18,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4578
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4579 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 22 104 273 161 193 129 385), lower := (rows 97 14 22 104 273 32 64 128 256), losses := [] }

theorem u4579 : Upper (D 3) (R 3) [96,12,18,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4579
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4580 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 22 104 400 161 193 129 385), lower := (rows 97 14 22 104 400 32 64 128 256), losses := [] }

theorem u4580 : Upper (D 3) (R 3) [96,12,18,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4580
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4581 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 22 137 145 353 353 481 353), lower := (rows 97 14 22 137 145 32 64 128 256), losses := [] }

theorem u4581 : Upper (D 3) (R 3) [96,12,18,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4581
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4582 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 22 137 176 353 321 449 321), lower := (rows 97 14 22 137 176 32 64 128 256), losses := [] }

theorem u4582 : Upper (D 3) (R 3) [96,12,18,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4582
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4583 : Route 9 := (fun mask => (mask,id))

def c4583 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4583 : Upper (D 3) (R 3) [96,12,18,129,257] 13 := by
  apply FastRouting.sound _ _ [96,12,18,129,257] 13 (by decide) (choices 1) [1,64,128] r4583 c4583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1696
  · exact u1697
  · exact u1698

def b4584 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 22 137 304 225 193 193 449), lower := (rows 97 14 22 137 304 32 64 128 256), losses := [] }

theorem u4584 : Upper (D 3) (R 3) [96,12,18,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4584
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4585 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 22 137 400 97 97 225 353), lower := (rows 97 14 22 137 400 32 64 128 256), losses := [] }

theorem u4585 : Upper (D 3) (R 3) [96,12,18,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4585
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4586 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 22 168 208 289 321 385 257), lower := (rows 97 14 22 168 208 32 64 128 256), losses := [] }

theorem u4586 : Upper (D 3) (R 3) [96,12,18,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4586
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4587 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 22 168 273 225 193 193 449), lower := (rows 97 14 22 168 273 32 64 128 256), losses := [] }

theorem u4587 : Upper (D 3) (R 3) [96,12,18,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4587
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4588 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 22 168 336 161 193 129 385), lower := (rows 97 14 22 168 336 32 64 128 256), losses := [] }

theorem u4588 : Upper (D 3) (R 3) [96,12,18,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4588
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4589 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 22 168 400 97 65 193 321), lower := (rows 97 14 22 168 400 32 64 128 256), losses := [] }

theorem u4589 : Upper (D 3) (R 3) [96,12,18,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4589
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4590 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 88 145 419 451 387 387), lower := (rows 97 14 37 88 145 32 64 128 256), losses := [] }

theorem u4590 : Upper (D 3) (R 3) [96,12,33,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4590
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4591 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 88 273 163 195 131 387), lower := (rows 97 14 37 88 273 32 64 128 256), losses := [] }

theorem u4591 : Upper (D 3) (R 3) [96,12,33,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4591
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4592 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 88 400 163 195 131 387), lower := (rows 97 14 37 88 400 32 64 128 256), losses := [] }

theorem u4592 : Upper (D 3) (R 3) [96,12,33,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4592
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4593 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 137 82 433 465 401 401), lower := (rows 97 14 37 137 82 32 64 128 256), losses := [] }

theorem u4593 : Upper (D 3) (R 3) [96,12,33,129,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4593
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4594 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 137 208 307 339 403 275), lower := (rows 97 14 37 137 208 32 64 128 256), losses := [] }

theorem u4594 : Upper (D 3) (R 3) [96,12,33,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4594
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4595 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 137 273 242 210 210 466), lower := (rows 97 14 37 137 273 32 64 128 256), losses := [] }

theorem u4595 : Upper (D 3) (R 3) [96,12,33,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4595
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4596 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 137 274 241 209 209 465), lower := (rows 97 14 37 137 274 32 64 128 256), losses := [] }

theorem u4596 : Upper (D 3) (R 3) [96,12,33,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4596
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4597 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 137 336 179 211 147 403), lower := (rows 97 14 37 137 336 32 64 128 256), losses := [] }

theorem u4597 : Upper (D 3) (R 3) [96,12,33,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4597
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4598 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 137 400 115 83 211 339), lower := (rows 97 14 37 137 400 32 64 128 256), losses := [] }

theorem u4598 : Upper (D 3) (R 3) [96,12,33,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4598
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4599 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 138 273 241 209 209 465), lower := (rows 97 14 37 138 273 32 64 128 256), losses := [] }

theorem u4599 : Upper (D 3) (R 3) [96,12,33,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4599
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4600 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 138 336 177 209 145 401), lower := (rows 97 14 37 138 336 32 64 128 256), losses := [] }

theorem u4600 : Upper (D 3) (R 3) [96,12,33,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4600
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4601 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 152 273 227 195 195 451), lower := (rows 97 14 37 152 273 32 64 128 256), losses := [] }

theorem u4601 : Upper (D 3) (R 3) [96,12,33,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4601
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4602 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 152 274 225 193 193 449), lower := (rows 97 14 37 152 274 32 64 128 256), losses := [] }

theorem u4602 : Upper (D 3) (R 3) [96,12,33,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4602
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4603 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 152 336 163 195 131 387), lower := (rows 97 14 37 152 336 32 64 128 256), losses := [] }

theorem u4603 : Upper (D 3) (R 3) [96,12,33,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4603
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4604 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 200 145 307 339 403 275), lower := (rows 97 14 37 200 145 32 64 128 256), losses := [] }

theorem u4604 : Upper (D 3) (R 3) [96,12,33,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4604
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4605 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 200 273 179 211 147 403), lower := (rows 97 14 37 200 273 32 64 128 256), losses := [] }

theorem u4605 : Upper (D 3) (R 3) [96,12,33,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4605
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4606 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 200 274 177 209 145 401), lower := (rows 97 14 37 200 274 32 64 128 256), losses := [] }

theorem u4606 : Upper (D 3) (R 3) [96,12,33,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4606
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4607 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 200 400 51 83 147 275), lower := (rows 97 14 37 200 400 32 64 128 256), losses := [] }

theorem u4607 : Upper (D 3) (R 3) [96,12,33,192,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4607
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4608 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 265 82 177 209 145 401), lower := (rows 97 14 37 265 82 32 64 128 256), losses := [] }

theorem u4608 : Upper (D 3) (R 3) [96,12,33,257,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4608
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4609 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 265 145 242 210 210 466), lower := (rows 97 14 37 265 145 32 64 128 256), losses := [] }

theorem u4609 : Upper (D 3) (R 3) [96,12,33,257,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4609
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4610 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 265 146 241 209 209 465), lower := (rows 97 14 37 265 146 32 64 128 256), losses := [] }

theorem u4610 : Upper (D 3) (R 3) [96,12,33,257,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4610
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4611 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 265 208 179 211 147 403), lower := (rows 97 14 37 265 208 32 64 128 256), losses := [] }

theorem u4611 : Upper (D 3) (R 3) [96,12,33,257,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4611
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4612 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 266 145 241 209 209 465), lower := (rows 97 14 37 266 145 32 64 128 256), losses := [] }

theorem u4612 : Upper (D 3) (R 3) [96,12,33,258,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4612
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4613 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 266 208 177 209 145 401), lower := (rows 97 14 37 266 208 32 64 128 256), losses := [] }

theorem u4613 : Upper (D 3) (R 3) [96,12,33,258,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4613
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4614 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 280 145 227 195 195 451), lower := (rows 97 14 37 280 145 32 64 128 256), losses := [] }

theorem u4614 : Upper (D 3) (R 3) [96,12,33,272,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4614
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4615 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 280 146 225 193 193 449), lower := (rows 97 14 37 280 146 32 64 128 256), losses := [] }

theorem u4615 : Upper (D 3) (R 3) [96,12,33,272,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4615
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4616 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 280 208 163 195 131 387), lower := (rows 97 14 37 280 208 32 64 128 256), losses := [] }

theorem u4616 : Upper (D 3) (R 3) [96,12,33,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4616
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4617 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 328 145 179 211 147 403), lower := (rows 97 14 37 328 145 32 64 128 256), losses := [] }

theorem u4617 : Upper (D 3) (R 3) [96,12,33,320,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4617
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4618 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 328 146 177 209 145 401), lower := (rows 97 14 37 328 146 32 64 128 256), losses := [] }

theorem u4618 : Upper (D 3) (R 3) [96,12,33,320,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4618
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4619 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 392 82 177 209 145 401), lower := (rows 97 14 37 392 82 32 64 128 256), losses := [] }

theorem u4619 : Upper (D 3) (R 3) [96,12,33,384,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4619
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4619
end Delivery.IrregularNine14.P03
