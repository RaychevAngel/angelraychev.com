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

def b4740 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 140 56 21 34 329 393 265), lower := (rows 35 70 140 56 21 34 64 128 256), losses := [] }

theorem u4740 : Upper (D 5) (R 5) [34,68,136,48,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4740
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4741 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 140 56 21 40 323 387 259), lower := (rows 35 70 140 56 21 40 64 128 256), losses := [] }

theorem u4741 : Upper (D 5) (R 5) [34,68,136,48,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4741
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4742 : Route 9 := (fun mask => (mask,id))

def c4742 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4742 : Upper (D 5) (R 5) [34,68,136,48,5,256] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,5,256] 13 (by decide) (choices 1) [1,2,8] r4742 c4742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1705
  · exact u1706
  · exact u1707

def b4743 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 140 56 273 33 78 142 270), lower := (rows 35 70 140 56 273 33 64 128 256), losses := [] }

theorem u4743 : Upper (D 5) (R 5) [34,68,136,48,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4743
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4744 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 140 56 273 34 77 141 269), lower := (rows 35 70 140 56 273 34 64 128 256), losses := [] }

theorem u4744 : Upper (D 5) (R 5) [34,68,136,48,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4744
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4745 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 140 56 273 36 75 139 267), lower := (rows 35 70 140 56 273 36 64 128 256), losses := [] }

theorem u4745 : Upper (D 5) (R 5) [34,68,136,48,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4745
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4746 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 140 56 273 40 71 135 263), lower := (rows 35 70 140 56 273 40 64 128 256), losses := [] }

theorem u4746 : Upper (D 5) (R 5) [34,68,136,48,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4746
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4747 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 140 56 274 33 77 141 269), lower := (rows 35 70 140 56 274 33 64 128 256), losses := [] }

theorem u4747 : Upper (D 5) (R 5) [34,68,136,48,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4747
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4748 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 140 56 274 36 73 137 265), lower := (rows 35 70 140 56 274 36 64 128 256), losses := [] }

theorem u4748 : Upper (D 5) (R 5) [34,68,136,48,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4748
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4749 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 140 56 274 40 69 133 261), lower := (rows 35 70 140 56 274 40 64 128 256), losses := [] }

theorem u4749 : Upper (D 5) (R 5) [34,68,136,48,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4749
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4750 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 140 56 276 33 75 139 267), lower := (rows 35 70 140 56 276 33 64 128 256), losses := [] }

theorem u4750 : Upper (D 5) (R 5) [34,68,136,48,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4750
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4751 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 140 56 276 34 73 137 265), lower := (rows 35 70 140 56 276 34 64 128 256), losses := [] }

theorem u4751 : Upper (D 5) (R 5) [34,68,136,48,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4751
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4752 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 140 56 276 40 67 131 259), lower := (rows 35 70 140 56 276 40 64 128 256), losses := [] }

theorem u4752 : Upper (D 5) (R 5) [34,68,136,48,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4752
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4753 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 140 265 21 34 120 184 312), lower := (rows 35 70 140 265 21 34 64 128 256), losses := [] }

theorem u4753 : Upper (D 5) (R 5) [34,68,136,257,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4753
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4754 : PairBound 9 := { available := 50, camps := [], pairs := [(0,2),(1,0)], upper := (rows 35 70 140 265 21 40 114 178 306), lower := (rows 35 70 140 265 21 40 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 44 80 144 272), good := (rows 34 102 172 296 502 40 64 128 256) },{ target := 2, region := (rows 3 2 0 8 16 44 64 128 256), good := (rows 35 99 168 297 49 40 64 128 256) }] }

theorem u4754 : Upper (D 5) (R 5) [34,68,136,257,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4754
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4755 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3)], upper := (rows 35 70 140 265 21 48 106 170 298), lower := (rows 35 70 140 265 21 48 64 128 256), losses := [] }

theorem u4755 : Upper (D 5) (R 5) [34,68,136,257,5,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4755
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4756 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 140 265 26 33 116 180 308), lower := (rows 35 70 140 265 26 33 64 128 256), losses := [] }

theorem u4756 : Upper (D 5) (R 5) [34,68,136,257,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4756
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4757 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 140 265 26 36 113 177 305), lower := (rows 35 70 140 265 26 36 64 128 256), losses := [] }

theorem u4757 : Upper (D 5) (R 5) [34,68,136,257,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4757
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4758 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 140 265 26 48 101 165 293), lower := (rows 35 70 140 265 26 48 64 128 256), losses := [] }

theorem u4758 : Upper (D 5) (R 5) [34,68,136,257,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4758
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4759 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 35 70 140 265 52 33 90 154 282), lower := (rows 35 70 140 265 52 33 64 128 256), losses := [] }

theorem u4759 : Upper (D 5) (R 5) [34,68,136,257,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4759
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4760 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 140 265 52 34 89 153 281), lower := (rows 35 70 140 265 52 34 64 128 256), losses := [] }

theorem u4760 : Upper (D 5) (R 5) [34,68,136,257,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4760
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4761 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 140 265 52 40 83 147 275), lower := (rows 35 70 140 265 52 40 64 128 256), losses := [] }

theorem u4761 : Upper (D 5) (R 5) [34,68,136,257,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4761
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4762 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 140 265 52 48 75 139 267), lower := (rows 35 70 140 265 52 48 64 128 256), losses := [] }

theorem u4762 : Upper (D 5) (R 5) [34,68,136,257,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4762
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4763 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 198, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 140 265 56 33 86 150 278), lower := (rows 35 70 140 265 56 33 64 128 256), losses := [] }

theorem u4763 : Upper (D 5) (R 5) [34,68,136,257,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4763
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4764 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 140 265 56 34 85 149 277), lower := (rows 35 70 140 265 56 34 64 128 256), losses := [] }

theorem u4764 : Upper (D 5) (R 5) [34,68,136,257,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4764
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4765 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 140 265 56 36 83 147 275), lower := (rows 35 70 140 265 56 36 64 128 256), losses := [] }

theorem u4765 : Upper (D 5) (R 5) [34,68,136,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4765
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4766 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 140 265 56 48 71 135 263), lower := (rows 35 70 140 265 56 48 64 128 256), losses := [] }

theorem u4766 : Upper (D 5) (R 5) [34,68,136,257,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4766
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4767 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 35 70 140 266 21 33 120 184 312), lower := (rows 35 70 140 266 21 33 64 128 256), losses := [] }

theorem u4767 : Upper (D 5) (R 5) [34,68,136,258,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4767
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4768 : Route 9 := (fun mask => (mask,id))

def c4768 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4768 : Upper (D 5) (R 5) [34,68,136,258,5,8] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,5,8] 13 (by decide) (choices 1) [1,16,32] r4768 c4768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1708
  · exact u1709
  · exact u1710

def b4769 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3)], upper := (rows 35 70 140 266 21 48 105 169 297), lower := (rows 35 70 140 266 21 48 64 128 256), losses := [] }

theorem u4769 : Upper (D 5) (R 5) [34,68,136,258,5,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4769
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4770 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 140 266 25 33 116 180 308), lower := (rows 35 70 140 266 25 33 64 128 256), losses := [] }

theorem u4770 : Upper (D 5) (R 5) [34,68,136,258,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4770
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4771 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 140 266 25 36 113 177 305), lower := (rows 35 70 140 266 25 36 64 128 256), losses := [] }

theorem u4771 : Upper (D 5) (R 5) [34,68,136,258,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4771
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4772 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 140 266 25 48 101 165 293), lower := (rows 35 70 140 266 25 48 64 128 256), losses := [] }

theorem u4772 : Upper (D 5) (R 5) [34,68,136,258,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4772
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4773 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 35 70 140 266 52 33 89 153 281), lower := (rows 35 70 140 266 52 33 64 128 256), losses := [] }

theorem u4773 : Upper (D 5) (R 5) [34,68,136,258,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4773
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4774 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 140 266 52 40 81 145 273), lower := (rows 35 70 140 266 52 40 64 128 256), losses := [] }

theorem u4774 : Upper (D 5) (R 5) [34,68,136,258,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4774
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4775 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 140 266 52 48 73 137 265), lower := (rows 35 70 140 266 52 48 64 128 256), losses := [] }

theorem u4775 : Upper (D 5) (R 5) [34,68,136,258,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4775
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4776 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 140 266 56 33 85 149 277), lower := (rows 35 70 140 266 56 33 64 128 256), losses := [] }

theorem u4776 : Upper (D 5) (R 5) [34,68,136,258,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4776
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4777 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 140 266 56 36 81 145 273), lower := (rows 35 70 140 266 56 36 64 128 256), losses := [] }

theorem u4777 : Upper (D 5) (R 5) [34,68,136,258,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4777
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4778 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 140 266 56 48 69 133 261), lower := (rows 35 70 140 266 56 48 64 128 256), losses := [] }

theorem u4778 : Upper (D 5) (R 5) [34,68,136,258,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4778
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4779 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 140 268 25 33 114 178 306), lower := (rows 35 70 140 268 25 33 64 128 256), losses := [] }

theorem u4779 : Upper (D 5) (R 5) [34,68,136,260,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4779
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4780 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 140 268 25 34 113 177 305), lower := (rows 35 70 140 268 25 34 64 128 256), losses := [] }

theorem u4780 : Upper (D 5) (R 5) [34,68,136,260,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4780
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4781 : Route 9 := (fun mask => (mask,id))

def c4781 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4781 : Upper (D 5) (R 5) [34,68,136,260,9,16] 13 := by
  apply FastRouting.sound _ _ [34,68,136,260,9,16] 13 (by decide) (choices 1) [1,2,32] r4781 c4781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1711
  · exact u1712
  · exact u1713

def b4782 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 140 268 56 33 83 147 275), lower := (rows 35 70 140 268 56 33 64 128 256), losses := [] }

theorem u4782 : Upper (D 5) (R 5) [34,68,136,260,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4782
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4783 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 140 268 56 34 81 145 273), lower := (rows 35 70 140 268 56 34 64 128 256), losses := [] }

theorem u4783 : Upper (D 5) (R 5) [34,68,136,260,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4783
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4784 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 140 268 56 48 67 131 259), lower := (rows 35 70 140 268 56 48 64 128 256), losses := [] }

theorem u4784 : Upper (D 5) (R 5) [34,68,136,260,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4784
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4785 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 35 70 140 280 21 33 106 170 298), lower := (rows 35 70 140 280 21 33 64 128 256), losses := [] }

theorem u4785 : Upper (D 5) (R 5) [34,68,136,272,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4785
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4786 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 140 280 21 34 105 169 297), lower := (rows 35 70 140 280 21 34 64 128 256), losses := [] }

theorem u4786 : Upper (D 5) (R 5) [34,68,136,272,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4786
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4787 : PairBound 9 := { available := 35, camps := [], pairs := [(0,2),(3,2)], upper := (rows 35 70 140 280 21 40 99 163 291), lower := (rows 35 70 140 280 21 40 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 24 16 60 67 131 259), good := (rows 483 483 168 312 505 40 64 128 256) }] }

theorem u4787 : Upper (D 5) (R 5) [34,68,136,272,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4787
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4788 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 35 70 140 280 52 33 75 139 267), lower := (rows 35 70 140 280 52 33 64 128 256), losses := [] }

theorem u4788 : Upper (D 5) (R 5) [34,68,136,272,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4788
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4789 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 140 280 52 34 73 137 265), lower := (rows 35 70 140 280 52 34 64 128 256), losses := [] }

theorem u4789 : Upper (D 5) (R 5) [34,68,136,272,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4789
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4790 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 140 280 52 40 67 131 259), lower := (rows 35 70 140 280 52 40 64 128 256), losses := [] }

theorem u4790 : Upper (D 5) (R 5) [34,68,136,272,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4790
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4791 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 35 70 140 296 21 33 90 154 282), lower := (rows 35 70 140 296 21 33 64 128 256), losses := [] }

theorem u4791 : Upper (D 5) (R 5) [34,68,136,288,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4791
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4792 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 140 296 21 34 89 153 281), lower := (rows 35 70 140 296 21 34 64 128 256), losses := [] }

theorem u4792 : Upper (D 5) (R 5) [34,68,136,288,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4792
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4793 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 140 296 21 40 83 147 275), lower := (rows 35 70 140 296 21 40 64 128 256), losses := [] }

theorem u4793 : Upper (D 5) (R 5) [34,68,136,288,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4793
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4794 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3)], upper := (rows 35 70 140 296 21 48 75 139 267), lower := (rows 35 70 140 296 21 48 64 128 256), losses := [] }

theorem u4794 : Upper (D 5) (R 5) [34,68,136,288,5,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4794
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4795 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 140 296 26 33 85 149 277), lower := (rows 35 70 140 296 26 33 64 128 256), losses := [] }

theorem u4795 : Upper (D 5) (R 5) [34,68,136,288,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4795
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4796 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 140 296 26 36 81 145 273), lower := (rows 35 70 140 296 26 36 64 128 256), losses := [] }

theorem u4796 : Upper (D 5) (R 5) [34,68,136,288,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4796
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4797 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 140 296 26 48 69 133 261), lower := (rows 35 70 140 296 26 48 64 128 256), losses := [] }

theorem u4797 : Upper (D 5) (R 5) [34,68,136,288,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4797
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4798 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 148 44 26 33 329 393 265), lower := (rows 35 70 148 44 26 33 64 128 256), losses := [] }

theorem u4798 : Upper (D 5) (R 5) [34,68,144,36,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4798
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4799 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 70 148 44 26 40 321 385 257), lower := (rows 35 70 148 44 26 40 64 128 256), losses := [] }

theorem u4799 : Upper (D 5) (R 5) [34,68,144,36,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4799
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u4799
end Delivery.IrregularNine14.P05
