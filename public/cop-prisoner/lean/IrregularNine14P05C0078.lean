import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0028

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4680 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 133 280 28 40 99 163 291), lower := (rows 35 70 133 280 28 40 64 128 256), losses := [] }

theorem u4680 : Upper (D 5) (R 5) [34,68,129,272,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4680
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4681 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 133 280 52 33 74 138 266), lower := (rows 35 70 133 280 52 33 64 128 256), losses := [] }

theorem u4681 : Upper (D 5) (R 5) [34,68,129,272,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4681
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4682 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 280 52 34 73 137 265), lower := (rows 35 70 133 280 52 34 64 128 256), losses := [] }

theorem u4682 : Upper (D 5) (R 5) [34,68,129,272,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4682
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4683 : Route 9 := (fun mask => (mask,id))

def c4683 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4683 : Upper (D 5) (R 5) [34,68,129,272,36,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,272,36,8] 13 (by decide) (choices 1) [1,2,8] r4683 c4683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1684
  · exact u1685
  · exact u1686

def b4684 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 133 280 56 33 78 142 270), lower := (rows 35 70 133 280 56 33 64 128 256), losses := [] }

theorem u4684 : Upper (D 5) (R 5) [34,68,129,272,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4684
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4685 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 280 56 34 77 141 269), lower := (rows 35 70 133 280 56 34 64 128 256), losses := [] }

theorem u4685 : Upper (D 5) (R 5) [34,68,129,272,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4685
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4686 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 133 280 56 36 75 139 267), lower := (rows 35 70 133 280 56 36 64 128 256), losses := [] }

theorem u4686 : Upper (D 5) (R 5) [34,68,129,272,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4686
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4687 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 133 280 56 40 71 135 263), lower := (rows 35 70 133 280 56 40 64 128 256), losses := [] }

theorem u4687 : Upper (D 5) (R 5) [34,68,129,272,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4687
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4688 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 133 296 26 33 92 156 284), lower := (rows 35 70 133 296 26 33 64 128 256), losses := [] }

theorem u4688 : Upper (D 5) (R 5) [34,68,129,288,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4688
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4689 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 133 296 26 36 89 153 281), lower := (rows 35 70 133 296 26 36 64 128 256), losses := [] }

theorem u4689 : Upper (D 5) (R 5) [34,68,129,288,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4689
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4690 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 133 296 26 40 85 149 277), lower := (rows 35 70 133 296 26 40 64 128 256), losses := [] }

theorem u4690 : Upper (D 5) (R 5) [34,68,129,288,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4690
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4691 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 133 296 26 48 77 141 269), lower := (rows 35 70 133 296 26 48 64 128 256), losses := [] }

theorem u4691 : Upper (D 5) (R 5) [34,68,129,288,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4691
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4692 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 133 296 28 33 90 154 282), lower := (rows 35 70 133 296 28 33 64 128 256), losses := [] }

theorem u4692 : Upper (D 5) (R 5) [34,68,129,288,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4692
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4693 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 296 28 34 89 153 281), lower := (rows 35 70 133 296 28 34 64 128 256), losses := [] }

theorem u4693 : Upper (D 5) (R 5) [34,68,129,288,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4693
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4694 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 133 296 28 40 83 147 275), lower := (rows 35 70 133 296 28 40 64 128 256), losses := [] }

theorem u4694 : Upper (D 5) (R 5) [34,68,129,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4694
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4695 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 264, targets := 4 }], pairs := [(3,2)], upper := (rows 35 70 133 296 28 48 75 139 267), lower := (rows 35 70 133 296 28 48 64 128 256), losses := [] }

theorem u4695 : Upper (D 5) (R 5) [34,68,129,288,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4695
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4696 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 134 44 273 33 88 152 280), lower := (rows 35 70 134 44 273 33 64 128 256), losses := [] }

theorem u4696 : Upper (D 5) (R 5) [34,68,130,36,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4696
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4697 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 134 44 273 40 89 153 281), lower := (rows 35 70 134 44 273 40 64 128 256), losses := [] }

theorem u4697 : Upper (D 5) (R 5) [34,68,130,36,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4697
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4698 : Route 9 := (fun mask => (mask,id))

def c4698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4698 : Upper (D 5) (R 5) [34,68,130,36,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,130,36,257,16] 13 (by decide) (choices 1) [1,8] r4698 c4698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1687
  · exact u1688

def b4699 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 134 56 28 33 329 393 265), lower := (rows 35 70 134 56 28 33 64 128 256), losses := [] }

theorem u4699 : Upper (D 5) (R 5) [34,68,130,48,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4699
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4700 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 454, targets := 40 }], pairs := [(1,3),(1,5)], upper := (rows 35 70 134 56 28 40 321 385 257), lower := (rows 35 70 134 56 28 40 64 128 256), losses := [] }

theorem u4700 : Upper (D 5) (R 5) [34,68,130,48,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4700
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4701 : Route 9 := (fun mask => (mask,id))

def c4701 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4701 : Upper (D 5) (R 5) [34,68,130,48,12,256] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,12,256] 13 (by decide) (choices 1) [1,8] r4701 c4701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1689
  · exact u1690

def b4702 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 134 56 273 33 76 140 268), lower := (rows 35 70 134 56 273 33 64 128 256), losses := [] }

theorem u4702 : Upper (D 5) (R 5) [34,68,130,48,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4702
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4703 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 134 56 273 36 73 137 265), lower := (rows 35 70 134 56 273 36 64 128 256), losses := [] }

theorem u4703 : Upper (D 5) (R 5) [34,68,130,48,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4703
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4704 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 134 56 273 40 77 141 269), lower := (rows 35 70 134 56 273 40 64 128 256), losses := [] }

theorem u4704 : Upper (D 5) (R 5) [34,68,130,48,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4704
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4705 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 134 56 276 33 73 137 265), lower := (rows 35 70 134 56 276 33 64 128 256), losses := [] }

theorem u4705 : Upper (D 5) (R 5) [34,68,130,48,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4705
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4706 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 134 56 276 40 73 137 265), lower := (rows 35 70 134 56 276 40 64 128 256), losses := [] }

theorem u4706 : Upper (D 5) (R 5) [34,68,130,48,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4706
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4707 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 134 56 280 33 77 141 269), lower := (rows 35 70 134 56 280 33 64 128 256), losses := [] }

theorem u4707 : Upper (D 5) (R 5) [34,68,130,48,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4707
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4708 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 134 56 280 36 73 137 265), lower := (rows 35 70 134 56 280 36 64 128 256), losses := [] }

theorem u4708 : Upper (D 5) (R 5) [34,68,130,48,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4708
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4709 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 134 56 280 40 69 133 261), lower := (rows 35 70 134 56 280 40 64 128 256), losses := [] }

theorem u4709 : Upper (D 5) (R 5) [34,68,130,48,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4709
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4710 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 134 265 28 33 120 184 312), lower := (rows 35 70 134 265 28 33 64 128 256), losses := [] }

theorem u4710 : Upper (D 5) (R 5) [34,68,130,257,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4710
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4711 : Route 9 := (fun mask => (mask,id))

def c4711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4711 : Upper (D 5) (R 5) [34,68,130,257,12,8] 13 := by
  apply FastRouting.sound _ _ [34,68,130,257,12,8] 13 (by decide) (choices 1) [1,16,32] r4711 c4711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1691
  · exact u1692
  · exact u1693

def b4712 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 264, targets := 2 }], pairs := [(3,1)], upper := (rows 35 70 134 265 28 48 105 169 297), lower := (rows 35 70 134 265 28 48 64 128 256), losses := [] }

theorem u4712 : Upper (D 5) (R 5) [34,68,130,257,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4712
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4713 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 35 70 134 265 52 33 88 152 280), lower := (rows 35 70 134 265 52 33 64 128 256), losses := [] }

theorem u4713 : Upper (D 5) (R 5) [34,68,130,257,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4713
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4714 : Route 9 := (fun mask => (mask,id))

def c4714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4714 : Upper (D 5) (R 5) [34,68,130,257,36,8] 13 := by
  apply FastRouting.sound _ _ [34,68,130,257,36,8] 13 (by decide) (choices 1) [1,8,16] r4714 c4714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1694
  · exact u1695
  · exact u1696

def b4715 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 134 265 52 48 73 137 265), lower := (rows 35 70 134 265 52 48 64 128 256), losses := [] }

theorem u4715 : Upper (D 5) (R 5) [34,68,130,257,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4715
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4716 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 198, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 134 265 56 33 92 156 284), lower := (rows 35 70 134 265 56 33 64 128 256), losses := [] }

theorem u4716 : Upper (D 5) (R 5) [34,68,130,257,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4716
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4717 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 280, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 134 265 56 36 89 153 281), lower := (rows 35 70 134 265 56 36 64 128 256), losses := [] }

theorem u4717 : Upper (D 5) (R 5) [34,68,130,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4717
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4718 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 134 265 56 40 85 149 277), lower := (rows 35 70 134 265 56 40 64 128 256), losses := [] }

theorem u4718 : Upper (D 5) (R 5) [34,68,130,257,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4718
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4719 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 134 265 56 48 77 141 269), lower := (rows 35 70 134 265 56 48 64 128 256), losses := [] }

theorem u4719 : Upper (D 5) (R 5) [34,68,130,257,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4719
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4720 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 134 268 25 33 120 184 312), lower := (rows 35 70 134 268 25 33 64 128 256), losses := [] }

theorem u4720 : Upper (D 5) (R 5) [34,68,130,260,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4720
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4721 : Route 9 := (fun mask => (mask,id))

def c4721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4721 : Upper (D 5) (R 5) [34,68,130,260,9,8] 13 := by
  apply FastRouting.sound _ _ [34,68,130,260,9,8] 13 (by decide) (choices 1) [1,16,32] r4721 c4721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1697
  · exact u1698
  · exact u1699

def r4722 : Route 9 := (fun mask => (mask,id))

def c4722 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4722 : Upper (D 5) (R 5) [34,68,130,260,9,16] 13 := by
  apply FastRouting.sound _ _ [34,68,130,260,9,16] 13 (by decide) (choices 1) [1,8,32] r4722 c4722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1700
  · exact u1701
  · exact u1702

def b4723 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 134 268 56 33 89 153 281), lower := (rows 35 70 134 268 56 33 64 128 256), losses := [] }

theorem u4723 : Upper (D 5) (R 5) [34,68,130,260,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4723
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4724 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 134 268 56 40 81 145 273), lower := (rows 35 70 134 268 56 40 64 128 256), losses := [] }

theorem u4724 : Upper (D 5) (R 5) [34,68,130,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4724
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4725 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 134 268 56 48 73 137 265), lower := (rows 35 70 134 268 56 48 64 128 256), losses := [] }

theorem u4725 : Upper (D 5) (R 5) [34,68,130,260,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4725
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4726 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 134 280 25 33 108 172 300), lower := (rows 35 70 134 280 25 33 64 128 256), losses := [] }

theorem u4726 : Upper (D 5) (R 5) [34,68,130,272,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4726
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4727 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 280, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 134 280 25 36 105 169 297), lower := (rows 35 70 134 280 25 36 64 128 256), losses := [] }

theorem u4727 : Upper (D 5) (R 5) [34,68,130,272,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4727
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4728 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 134 280 25 40 101 165 293), lower := (rows 35 70 134 280 25 40 64 128 256), losses := [] }

theorem u4728 : Upper (D 5) (R 5) [34,68,130,272,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4728
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4729 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 134 280 28 33 105 169 297), lower := (rows 35 70 134 280 28 33 64 128 256), losses := [] }

theorem u4729 : Upper (D 5) (R 5) [34,68,130,272,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4729
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4730 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 134 280 28 40 97 161 289), lower := (rows 35 70 134 280 28 40 64 128 256), losses := [] }

theorem u4730 : Upper (D 5) (R 5) [34,68,130,272,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4730
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4731 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 35 70 134 280 52 33 73 137 265), lower := (rows 35 70 134 280 52 33 64 128 256), losses := [] }

theorem u4731 : Upper (D 5) (R 5) [34,68,130,272,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4731
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4732 : Route 9 := (fun mask => (mask,id))

def c4732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4732 : Upper (D 5) (R 5) [34,68,130,272,36,8] 13 := by
  apply FastRouting.sound _ _ [34,68,130,272,36,8] 13 (by decide) (choices 1) [1,8] r4732 c4732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1703
  · exact u1704

def b4733 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 134 280 56 33 77 141 269), lower := (rows 35 70 134 280 56 33 64 128 256), losses := [] }

theorem u4733 : Upper (D 5) (R 5) [34,68,130,272,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4733
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4734 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 134 280 56 36 73 137 265), lower := (rows 35 70 134 280 56 36 64 128 256), losses := [] }

theorem u4734 : Upper (D 5) (R 5) [34,68,130,272,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4734
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4735 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 134 280 56 40 69 133 261), lower := (rows 35 70 134 280 56 40 64 128 256), losses := [] }

theorem u4735 : Upper (D 5) (R 5) [34,68,130,272,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4735
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4736 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 134 296 28 33 89 153 281), lower := (rows 35 70 134 296 28 33 64 128 256), losses := [] }

theorem u4736 : Upper (D 5) (R 5) [34,68,130,288,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4736
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4737 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 134 296 28 40 81 145 273), lower := (rows 35 70 134 296 28 40 64 128 256), losses := [] }

theorem u4737 : Upper (D 5) (R 5) [34,68,130,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4737
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4738 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 2 }], pairs := [(3,1)], upper := (rows 35 70 134 296 28 48 73 137 265), lower := (rows 35 70 134 296 28 48 64 128 256), losses := [] }

theorem u4738 : Upper (D 5) (R 5) [34,68,130,288,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4738
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4739 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 140 56 21 33 330 394 266), lower := (rows 35 70 140 56 21 33 64 128 256), losses := [] }

theorem u4739 : Upper (D 5) (R 5) [34,68,136,48,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4739
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u4739
end Delivery.IrregularNine14.P05
