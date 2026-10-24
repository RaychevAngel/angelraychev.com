import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0028

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4620 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 392 145 115 83 211 339), lower := (rows 97 14 37 392 145 32 64 128 256), losses := [] }

theorem u4620 : Upper (D 3) (R 3) [96,12,33,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4620
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4621 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 37 392 208 51 83 147 275), lower := (rows 97 14 37 392 208 32 64 128 256), losses := [] }

theorem u4621 : Upper (D 3) (R 3) [96,12,33,384,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4621
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4622 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 88 145 417 449 385 385), lower := (rows 97 14 38 88 145 32 64 128 256), losses := [] }

theorem u4622 : Upper (D 3) (R 3) [96,12,34,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4622
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4623 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 88 273 161 193 129 385), lower := (rows 97 14 38 88 273 32 64 128 256), losses := [] }

theorem u4623 : Upper (D 3) (R 3) [96,12,34,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4623
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4624 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 88 400 161 193 129 385), lower := (rows 97 14 38 88 400 32 64 128 256), losses := [] }

theorem u4624 : Upper (D 3) (R 3) [96,12,34,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4624
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4625 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 137 208 305 337 401 273), lower := (rows 97 14 38 137 208 32 64 128 256), losses := [] }

theorem u4625 : Upper (D 3) (R 3) [96,12,34,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4625
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4626 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 137 273 241 209 209 465), lower := (rows 97 14 38 137 273 32 64 128 256), losses := [] }

theorem u4626 : Upper (D 3) (R 3) [96,12,34,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4626
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4627 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 137 336 177 209 145 401), lower := (rows 97 14 38 137 336 32 64 128 256), losses := [] }

theorem u4627 : Upper (D 3) (R 3) [96,12,34,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4627
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4628 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 137 400 113 81 209 337), lower := (rows 97 14 38 137 400 32 64 128 256), losses := [] }

theorem u4628 : Upper (D 3) (R 3) [96,12,34,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4628
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4629 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 152 273 225 193 193 449), lower := (rows 97 14 38 152 273 32 64 128 256), losses := [] }

theorem u4629 : Upper (D 3) (R 3) [96,12,34,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4629
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4630 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 152 336 161 193 129 385), lower := (rows 97 14 38 152 336 32 64 128 256), losses := [] }

theorem u4630 : Upper (D 3) (R 3) [96,12,34,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4630
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4631 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 200 145 305 337 401 273), lower := (rows 97 14 38 200 145 32 64 128 256), losses := [] }

theorem u4631 : Upper (D 3) (R 3) [96,12,34,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4631
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4632 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 200 273 177 209 145 401), lower := (rows 97 14 38 200 273 32 64 128 256), losses := [] }

theorem u4632 : Upper (D 3) (R 3) [96,12,34,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4632
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4633 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 200 400 49 81 145 273), lower := (rows 97 14 38 200 400 32 64 128 256), losses := [] }

theorem u4633 : Upper (D 3) (R 3) [96,12,34,192,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4633
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4634 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 265 145 241 209 209 465), lower := (rows 97 14 38 265 145 32 64 128 256), losses := [] }

theorem u4634 : Upper (D 3) (R 3) [96,12,34,257,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4634
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4635 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 265 208 177 209 145 401), lower := (rows 97 14 38 265 208 32 64 128 256), losses := [] }

theorem u4635 : Upper (D 3) (R 3) [96,12,34,257,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4635
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4636 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 280 145 225 193 193 449), lower := (rows 97 14 38 280 145 32 64 128 256), losses := [] }

theorem u4636 : Upper (D 3) (R 3) [96,12,34,272,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4636
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4637 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 280 208 161 193 129 385), lower := (rows 97 14 38 280 208 32 64 128 256), losses := [] }

theorem u4637 : Upper (D 3) (R 3) [96,12,34,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4637
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4638 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 328 145 177 209 145 401), lower := (rows 97 14 38 328 145 32 64 128 256), losses := [] }

theorem u4638 : Upper (D 3) (R 3) [96,12,34,320,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4638
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4639 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 392 145 113 81 209 337), lower := (rows 97 14 38 392 145 32 64 128 256), losses := [] }

theorem u4639 : Upper (D 3) (R 3) [96,12,34,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4639
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4640 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 392 208 49 81 145 273), lower := (rows 97 14 38 392 208 32 64 128 256), losses := [] }

theorem u4640 : Upper (D 3) (R 3) [96,12,34,384,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4640
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4641 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 137 81 419 451 387 387), lower := (rows 97 14 52 137 81 32 64 128 256), losses := [] }

theorem u4641 : Upper (D 3) (R 3) [96,12,48,129,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4641
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4642 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 52 137 82 417 449 385 385), lower := (rows 97 14 52 137 82 32 64 128 256), losses := [] }

theorem u4642 : Upper (D 3) (R 3) [96,12,48,129,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4642
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4643 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 52 137 145 355 323 451 323), lower := (rows 97 14 52 137 145 32 64 128 256), losses := [] }

theorem u4643 : Upper (D 3) (R 3) [96,12,48,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4643
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4644 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 146 353 321 449 321), lower := (rows 97 14 52 137 146 32 64 128 256), losses := [] }

theorem u4644 : Upper (D 3) (R 3) [96,12,48,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4644
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4645 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 208 291 323 387 259), lower := (rows 97 14 52 137 208 32 64 128 256), losses := [] }

theorem u4645 : Upper (D 3) (R 3) [96,12,48,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4645
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4646 : Route 9 := (fun mask => (mask,id))

def c4646 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4646 : Upper (D 3) (R 3) [96,12,48,129,257] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,257] 13 (by decide) (choices 1) [1,2,64,128] r4646 c4646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1699
  · exact u1700
  · exact u1701
  · exact u1702

def b4647 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 52 137 274 225 193 193 449), lower := (rows 97 14 52 137 274 32 64 128 256), losses := [] }

theorem u4647 : Upper (D 3) (R 3) [96,12,48,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4647
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4648 : Route 9 := (fun mask => (mask,id))

def c4648 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4648 : Upper (D 3) (R 3) [96,12,48,129,320] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,320] 13 (by decide) (choices 1) [1,2,128] r4648 c4648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1703
  · exact u1704
  · exact u1705

def b4649 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 400 99 67 195 323), lower := (rows 97 14 52 137 400 32 64 128 256), losses := [] }

theorem u4649 : Upper (D 3) (R 3) [96,12,48,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4649
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4650 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 138 145 353 321 449 321), lower := (rows 97 14 52 138 145 32 64 128 256), losses := [] }

theorem u4650 : Upper (D 3) (R 3) [96,12,48,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4650
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4651 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 138 208 289 321 385 257), lower := (rows 97 14 52 138 208 32 64 128 256), losses := [] }

theorem u4651 : Upper (D 3) (R 3) [96,12,48,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4651
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4652 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 52 138 273 225 193 193 449), lower := (rows 97 14 52 138 273 32 64 128 256), losses := [] }

theorem u4652 : Upper (D 3) (R 3) [96,12,48,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4652
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4653 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 52 138 336 161 193 129 385), lower := (rows 97 14 52 138 336 32 64 128 256), losses := [] }

theorem u4653 : Upper (D 3) (R 3) [96,12,48,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4653
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4654 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 138 400 97 65 193 321), lower := (rows 97 14 52 138 400 32 64 128 256), losses := [] }

theorem u4654 : Upper (D 3) (R 3) [96,12,48,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4654
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4655 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 200 145 291 323 387 259), lower := (rows 97 14 52 200 145 32 64 128 256), losses := [] }

theorem u4655 : Upper (D 3) (R 3) [96,12,48,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4655
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4656 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 200 146 289 321 385 257), lower := (rows 97 14 52 200 146 32 64 128 256), losses := [] }

theorem u4656 : Upper (D 3) (R 3) [96,12,48,192,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4656
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4657 : Route 9 := (fun mask => (mask,id))

def c4657 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4657 : Upper (D 3) (R 3) [96,12,48,192,257] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,257] 13 (by decide) (choices 1) [1,2,128] r4657 c4657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1706
  · exact u1707
  · exact u1708

def b4658 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 52 200 274 161 193 129 385), lower := (rows 97 14 52 200 274 32 64 128 256), losses := [] }

theorem u4658 : Upper (D 3) (R 3) [96,12,48,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4658
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4659 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 200 400 35 67 131 259), lower := (rows 97 14 52 200 400 32 64 128 256), losses := [] }

theorem u4659 : Upper (D 3) (R 3) [96,12,48,192,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4659
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4660 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 265 81 163 195 131 387), lower := (rows 97 14 52 265 81 32 64 128 256), losses := [] }

theorem u4660 : Upper (D 3) (R 3) [96,12,48,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4660
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4661 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 52 265 82 161 193 129 385), lower := (rows 97 14 52 265 82 32 64 128 256), losses := [] }

theorem u4661 : Upper (D 3) (R 3) [96,12,48,257,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4661
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4662 : Route 9 := (fun mask => (mask,id))

def c4662 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4662 : Upper (D 3) (R 3) [96,12,48,257,129] 13 := by
  apply FastRouting.sound _ _ [96,12,48,257,129] 13 (by decide) (choices 1) [1,2,64,128] r4662 c4662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1709
  · exact u1710
  · exact u1711
  · exact u1712

def b4663 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 52 265 146 225 193 193 449), lower := (rows 97 14 52 265 146 32 64 128 256), losses := [] }

theorem u4663 : Upper (D 3) (R 3) [96,12,48,257,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4663
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4664 : Route 9 := (fun mask => (mask,id))

def c4664 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4664 : Upper (D 3) (R 3) [96,12,48,257,192] 13 := by
  apply FastRouting.sound _ _ [96,12,48,257,192] 13 (by decide) (choices 1) [1,2,128] r4664 c4664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1713
  · exact u1714
  · exact u1715

def b4665 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 52 266 145 225 193 193 449), lower := (rows 97 14 52 266 145 32 64 128 256), losses := [] }

theorem u4665 : Upper (D 3) (R 3) [96,12,48,258,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4665
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4666 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 52 266 208 161 193 129 385), lower := (rows 97 14 52 266 208 32 64 128 256), losses := [] }

theorem u4666 : Upper (D 3) (R 3) [96,12,48,258,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4666
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4667 : Route 9 := (fun mask => (mask,id))

def c4667 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4667 : Upper (D 3) (R 3) [96,12,48,320,129] 13 := by
  apply FastRouting.sound _ _ [96,12,48,320,129] 13 (by decide) (choices 1) [1,2,128] r4667 c4667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1716
  · exact u1717
  · exact u1718

def b4668 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 52 328 146 161 193 129 385), lower := (rows 97 14 52 328 146 32 64 128 256), losses := [] }

theorem u4668 : Upper (D 3) (R 3) [96,12,48,320,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4668
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4669 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 392 81 163 195 131 387), lower := (rows 97 14 52 392 81 32 64 128 256), losses := [] }

theorem u4669 : Upper (D 3) (R 3) [96,12,48,384,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4669
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4670 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 52 392 82 161 193 129 385), lower := (rows 97 14 52 392 82 32 64 128 256), losses := [] }

theorem u4670 : Upper (D 3) (R 3) [96,12,48,384,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4670
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4671 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 392 145 99 67 195 323), lower := (rows 97 14 52 392 145 32 64 128 256), losses := [] }

theorem u4671 : Upper (D 3) (R 3) [96,12,48,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4671
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4672 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 392 146 97 65 193 321), lower := (rows 97 14 52 392 146 32 64 128 256), losses := [] }

theorem u4672 : Upper (D 3) (R 3) [96,12,48,384,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4672
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4673 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 392 208 35 67 131 259), lower := (rows 97 14 52 392 208 32 64 128 256), losses := [] }

theorem u4673 : Upper (D 3) (R 3) [96,12,48,384,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4673
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4674 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 137 273 179 211 147 403), lower := (rows 97 14 100 137 273 32 64 128 256), losses := [] }

theorem u4674 : Upper (D 3) (R 3) [96,12,96,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4674
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4675 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 137 274 177 209 145 401), lower := (rows 97 14 100 137 274 32 64 128 256), losses := [] }

theorem u4675 : Upper (D 3) (R 3) [96,12,96,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4675
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4676 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 137 400 51 83 147 275), lower := (rows 97 14 100 137 400 32 64 128 256), losses := [] }

theorem u4676 : Upper (D 3) (R 3) [96,12,96,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4676
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4677 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 138 273 177 209 145 401), lower := (rows 97 14 100 138 273 32 64 128 256), losses := [] }

theorem u4677 : Upper (D 3) (R 3) [96,12,96,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4677
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4678 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 152 273 163 195 131 387), lower := (rows 97 14 100 152 273 32 64 128 256), losses := [] }

theorem u4678 : Upper (D 3) (R 3) [96,12,96,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4678
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4679 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 152 274 161 193 129 385), lower := (rows 97 14 100 152 274 32 64 128 256), losses := [] }

theorem u4679 : Upper (D 3) (R 3) [96,12,96,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4679
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4679
end Delivery.IrregularNine14.P03
