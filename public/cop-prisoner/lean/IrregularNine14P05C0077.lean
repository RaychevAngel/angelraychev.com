import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0027
import IrregularNine14P05C0028

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4620 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 56 28 34 329 393 265), lower := (rows 35 70 133 56 28 34 64 128 256), losses := [] }

theorem u4620 : Upper (D 5) (R 5) [34,68,129,48,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4620
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4621 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 454, targets := 40 }], pairs := [(1,3),(1,5)], upper := (rows 35 70 133 56 28 40 323 387 259), lower := (rows 35 70 133 56 28 40 64 128 256), losses := [] }

theorem u4621 : Upper (D 5) (R 5) [34,68,129,48,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4621
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4622 : Route 9 := (fun mask => (mask,id))

def c4622 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4622 : Upper (D 5) (R 5) [34,68,129,48,12,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,12,256] 13 (by decide) (choices 1) [1,2,8] r4622 c4622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1657
  · exact u1658
  · exact u1659

def b4623 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 56 273 34 76 140 268), lower := (rows 35 70 133 56 273 34 64 128 256), losses := [] }

theorem u4623 : Upper (D 5) (R 5) [34,68,129,48,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4623
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4624 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 133 56 273 36 74 138 266), lower := (rows 35 70 133 56 273 36 64 128 256), losses := [] }

theorem u4624 : Upper (D 5) (R 5) [34,68,129,48,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4624
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4625 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 133 56 273 40 78 142 270), lower := (rows 35 70 133 56 273 40 64 128 256), losses := [] }

theorem u4625 : Upper (D 5) (R 5) [34,68,129,48,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4625
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4626 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 133 56 274 33 76 140 268), lower := (rows 35 70 133 56 274 33 64 128 256), losses := [] }

theorem u4626 : Upper (D 5) (R 5) [34,68,129,48,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4626
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4627 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 133 56 274 36 73 137 265), lower := (rows 35 70 133 56 274 36 64 128 256), losses := [] }

theorem u4627 : Upper (D 5) (R 5) [34,68,129,48,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4627
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4628 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 133 56 274 40 77 141 269), lower := (rows 35 70 133 56 274 40 64 128 256), losses := [] }

theorem u4628 : Upper (D 5) (R 5) [34,68,129,48,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4628
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4629 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 133 56 276 33 74 138 266), lower := (rows 35 70 133 56 276 33 64 128 256), losses := [] }

theorem u4629 : Upper (D 5) (R 5) [34,68,129,48,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4629
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4630 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 56 276 34 73 137 265), lower := (rows 35 70 133 56 276 34 64 128 256), losses := [] }

theorem u4630 : Upper (D 5) (R 5) [34,68,129,48,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4630
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4631 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 133 56 276 40 75 139 267), lower := (rows 35 70 133 56 276 40 64 128 256), losses := [] }

theorem u4631 : Upper (D 5) (R 5) [34,68,129,48,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4631
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4632 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 133 56 280 33 78 142 270), lower := (rows 35 70 133 56 280 33 64 128 256), losses := [] }

theorem u4632 : Upper (D 5) (R 5) [34,68,129,48,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4632
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4633 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 56 280 34 77 141 269), lower := (rows 35 70 133 56 280 34 64 128 256), losses := [] }

theorem u4633 : Upper (D 5) (R 5) [34,68,129,48,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4633
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4634 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 133 56 280 36 75 139 267), lower := (rows 35 70 133 56 280 36 64 128 256), losses := [] }

theorem u4634 : Upper (D 5) (R 5) [34,68,129,48,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4634
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4635 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 133 56 280 40 71 135 263), lower := (rows 35 70 133 56 280 40 64 128 256), losses := [] }

theorem u4635 : Upper (D 5) (R 5) [34,68,129,48,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4635
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4636 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 133 265 26 36 120 184 312), lower := (rows 35 70 133 265 26 36 64 128 256), losses := [] }

theorem u4636 : Upper (D 5) (R 5) [34,68,129,257,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4636
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4637 : Route 9 := (fun mask => (mask,id))

def c4637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4637 : Upper (D 5) (R 5) [34,68,129,257,10,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257,10,8] 13 (by decide) (choices 1) [4,16,32] r4637 c4637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1660
  · exact u1661
  · exact u1662

def b4638 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 133 265 26 48 108 172 300), lower := (rows 35 70 133 265 26 48 64 128 256), losses := [] }

theorem u4638 : Upper (D 5) (R 5) [34,68,129,257,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4638
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4639 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 265 28 34 120 184 312), lower := (rows 35 70 133 265 28 34 64 128 256), losses := [] }

theorem u4639 : Upper (D 5) (R 5) [34,68,129,257,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4639
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4640 : Route 9 := (fun mask => (mask,id))

def c4640 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4640 : Upper (D 5) (R 5) [34,68,129,257,12,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257,12,8] 13 (by decide) (choices 1) [2,16,32] r4640 c4640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1663
  · exact u1664
  · exact u1665

def b4641 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 264, targets := 4 }], pairs := [(3,2)], upper := (rows 35 70 133 265 28 48 106 170 298), lower := (rows 35 70 133 265 28 48 64 128 256), losses := [] }

theorem u4641 : Upper (D 5) (R 5) [34,68,129,257,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4641
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4642 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 265 52 34 88 152 280), lower := (rows 35 70 133 265 52 34 64 128 256), losses := [] }

theorem u4642 : Upper (D 5) (R 5) [34,68,129,257,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4642
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4643 : Route 9 := (fun mask => (mask,id))

def c4643 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4643 : Upper (D 5) (R 5) [34,68,129,257,36,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257,36,8] 13 (by decide) (choices 1) [2,8,16] r4643 c4643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1666
  · exact u1667
  · exact u1668

def b4644 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 265 52 48 74 138 266), lower := (rows 35 70 133 265 52 48 64 128 256), losses := [] }

theorem u4644 : Upper (D 5) (R 5) [34,68,129,257,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4644
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4645 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 265 56 34 92 156 284), lower := (rows 35 70 133 265 56 34 64 128 256), losses := [] }

theorem u4645 : Upper (D 5) (R 5) [34,68,129,257,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4645
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4646 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 133 265 56 36 90 154 282), lower := (rows 35 70 133 265 56 36 64 128 256), losses := [] }

theorem u4646 : Upper (D 5) (R 5) [34,68,129,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4646
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4647 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 133 265 56 40 86 150 278), lower := (rows 35 70 133 265 56 40 64 128 256), losses := [] }

theorem u4647 : Upper (D 5) (R 5) [34,68,129,257,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4647
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4648 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 265 56 48 78 142 270), lower := (rows 35 70 133 265 56 48 64 128 256), losses := [] }

theorem u4648 : Upper (D 5) (R 5) [34,68,129,257,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4648
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4649 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 133 266 25 36 120 184 312), lower := (rows 35 70 133 266 25 36 64 128 256), losses := [] }

theorem u4649 : Upper (D 5) (R 5) [34,68,129,258,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4649
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4650 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 70 133 266 25 40 116 180 308), lower := (rows 35 70 133 266 25 40 64 128 256), losses := [] }

theorem u4650 : Upper (D 5) (R 5) [34,68,129,258,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4650
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4651 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 133 266 25 48 108 172 300), lower := (rows 35 70 133 266 25 48 64 128 256), losses := [] }

theorem u4651 : Upper (D 5) (R 5) [34,68,129,258,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4651
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4652 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 133 266 28 33 120 184 312), lower := (rows 35 70 133 266 28 33 64 128 256), losses := [] }

theorem u4652 : Upper (D 5) (R 5) [34,68,129,258,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4652
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4653 : Route 9 := (fun mask => (mask,id))

def c4653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4653 : Upper (D 5) (R 5) [34,68,129,258,12,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,258,12,8] 13 (by decide) (choices 1) [1,16,32] r4653 c4653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1669
  · exact u1670
  · exact u1671

def b4654 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 264, targets := 4 }], pairs := [(3,2)], upper := (rows 35 70 133 266 28 48 105 169 297), lower := (rows 35 70 133 266 28 48 64 128 256), losses := [] }

theorem u4654 : Upper (D 5) (R 5) [34,68,129,258,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4654
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4655 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 133 266 52 33 88 152 280), lower := (rows 35 70 133 266 52 33 64 128 256), losses := [] }

theorem u4655 : Upper (D 5) (R 5) [34,68,129,258,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4655
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4656 : Route 9 := (fun mask => (mask,id))

def c4656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4656 : Upper (D 5) (R 5) [34,68,129,258,36,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,258,36,8] 13 (by decide) (choices 1) [1,8,16] r4656 c4656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1672
  · exact u1673
  · exact u1674

def b4657 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 266 52 48 73 137 265), lower := (rows 35 70 133 266 52 48 64 128 256), losses := [] }

theorem u4657 : Upper (D 5) (R 5) [34,68,129,258,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4657
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4658 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 133 266 56 33 92 156 284), lower := (rows 35 70 133 266 56 33 64 128 256), losses := [] }

theorem u4658 : Upper (D 5) (R 5) [34,68,129,258,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4658
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4659 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 133 266 56 36 89 153 281), lower := (rows 35 70 133 266 56 36 64 128 256), losses := [] }

theorem u4659 : Upper (D 5) (R 5) [34,68,129,258,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4659
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4660 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 133 266 56 40 85 149 277), lower := (rows 35 70 133 266 56 40 64 128 256), losses := [] }

theorem u4660 : Upper (D 5) (R 5) [34,68,129,258,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4660
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4661 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 266 56 48 77 141 269), lower := (rows 35 70 133 266 56 48 64 128 256), losses := [] }

theorem u4661 : Upper (D 5) (R 5) [34,68,129,258,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4661
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4662 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 268 25 34 120 184 312), lower := (rows 35 70 133 268 25 34 64 128 256), losses := [] }

theorem u4662 : Upper (D 5) (R 5) [34,68,129,260,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4662
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4663 : Route 9 := (fun mask => (mask,id))

def c4663 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4663 : Upper (D 5) (R 5) [34,68,129,260,9,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,260,9,8] 13 (by decide) (choices 1) [2,16,32] r4663 c4663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1675
  · exact u1676
  · exact u1677

def r4664 : Route 9 := (fun mask => (mask,id))

def c4664 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4664 : Upper (D 5) (R 5) [34,68,129,260,9,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,260,9,16] 13 (by decide) (choices 1) [2,8,32] r4664 c4664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1678
  · exact u1679
  · exact u1680

def b4665 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 133 268 26 33 120 184 312), lower := (rows 35 70 133 268 26 33 64 128 256), losses := [] }

theorem u4665 : Upper (D 5) (R 5) [34,68,129,260,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4665
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4666 : Route 9 := (fun mask => (mask,id))

def c4666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4666 : Upper (D 5) (R 5) [34,68,129,260,10,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,260,10,8] 13 (by decide) (choices 1) [1,16,32] r4666 c4666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1681
  · exact u1682
  · exact u1683

def b4667 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 133 268 26 48 105 169 297), lower := (rows 35 70 133 268 26 48 64 128 256), losses := [] }

theorem u4667 : Upper (D 5) (R 5) [34,68,129,260,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4667
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4668 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 133 268 56 33 90 154 282), lower := (rows 35 70 133 268 56 33 64 128 256), losses := [] }

theorem u4668 : Upper (D 5) (R 5) [34,68,129,260,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4668
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4669 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 268 56 34 89 153 281), lower := (rows 35 70 133 268 56 34 64 128 256), losses := [] }

theorem u4669 : Upper (D 5) (R 5) [34,68,129,260,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4669
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4670 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 133 268 56 40 83 147 275), lower := (rows 35 70 133 268 56 40 64 128 256), losses := [] }

theorem u4670 : Upper (D 5) (R 5) [34,68,129,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4670
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4671 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 268 56 48 75 139 267), lower := (rows 35 70 133 268 56 48 64 128 256), losses := [] }

theorem u4671 : Upper (D 5) (R 5) [34,68,129,260,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4671
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4672 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 280 25 34 108 172 300), lower := (rows 35 70 133 280 25 34 64 128 256), losses := [] }

theorem u4672 : Upper (D 5) (R 5) [34,68,129,272,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4672
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4673 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 133 280 25 36 106 170 298), lower := (rows 35 70 133 280 25 36 64 128 256), losses := [] }

theorem u4673 : Upper (D 5) (R 5) [34,68,129,272,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4673
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4674 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 133 280 25 40 102 166 294), lower := (rows 35 70 133 280 25 40 64 128 256), losses := [] }

theorem u4674 : Upper (D 5) (R 5) [34,68,129,272,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4674
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4675 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 133 280 26 33 108 172 300), lower := (rows 35 70 133 280 26 33 64 128 256), losses := [] }

theorem u4675 : Upper (D 5) (R 5) [34,68,129,272,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4675
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4676 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 133 280 26 36 105 169 297), lower := (rows 35 70 133 280 26 36 64 128 256), losses := [] }

theorem u4676 : Upper (D 5) (R 5) [34,68,129,272,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4676
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4677 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 133 280 26 40 101 165 293), lower := (rows 35 70 133 280 26 40 64 128 256), losses := [] }

theorem u4677 : Upper (D 5) (R 5) [34,68,129,272,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4677
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4678 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 133 280 28 33 106 170 298), lower := (rows 35 70 133 280 28 33 64 128 256), losses := [] }

theorem u4678 : Upper (D 5) (R 5) [34,68,129,272,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4678
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4679 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 280 28 34 105 169 297), lower := (rows 35 70 133 280 28 34 64 128 256), losses := [] }

theorem u4679 : Upper (D 5) (R 5) [34,68,129,272,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4679
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u4679
end Delivery.IrregularNine14.P05
