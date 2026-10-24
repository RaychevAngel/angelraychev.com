import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0023

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4740 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 275 38 69 200 24 178 242 178 434), lower := (rows 275 38 69 200 24 32 64 128 256), losses := [] }

theorem u4740 : Upper (D 1) (R 1) [274,36,65,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4740
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4741 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 69 200 48 186 218 154 410), lower := (rows 275 38 69 200 48 32 64 128 256), losses := [] }

theorem u4741 : Upper (D 1) (R 1) [274,36,65,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4741
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4742 : Route 9 := (fun mask => (mask,id))

def c4742 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4742 : Upper (D 1) (R 1) [274,36,65,192,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,192,128] 13 (by decide) (choices 1) [2,8,16] r4742 c4742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1397
  · exact u1398
  · exact u1399

def b4743 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 76 137 18 240 240 240 496), lower := (rows 275 38 76 137 18 32 64 128 256), losses := [] }

theorem u4743 : Upper (D 1) (R 1) [274,36,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4743
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4744 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 76 137 48 242 210 210 466), lower := (rows 275 38 76 137 48 32 64 128 256), losses := [] }

theorem u4744 : Upper (D 1) (R 1) [274,36,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4744
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4745 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 76 137 80 178 242 178 434), lower := (rows 275 38 76 137 80 32 64 128 256), losses := [] }

theorem u4745 : Upper (D 1) (R 1) [274,36,72,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4745
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4746 : PairBound 9 := { available := 114, camps := [], pairs := [(1,7)], upper := (rows 275 38 76 137 144 114 114 242 370), lower := (rows 275 38 76 137 144 32 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 33 65 0 257), good := (rows 371 38 78 367 16 32 64 0 256) }] }

theorem u4746 : Upper (D 1) (R 1) [274,36,72,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4746
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4747 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 275 38 76 138 17 240 240 240 496), lower := (rows 275 38 76 138 17 32 64 128 256), losses := [] }

theorem u4747 : Upper (D 1) (R 1) [274,36,72,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4747
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4748 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 76 138 48 241 209 209 465), lower := (rows 275 38 76 138 48 32 64 128 256), losses := [] }

theorem u4748 : Upper (D 1) (R 1) [274,36,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4748
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4749 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 76 138 80 177 241 177 433), lower := (rows 275 38 76 138 80 32 64 128 256), losses := [] }

theorem u4749 : Upper (D 1) (R 1) [274,36,72,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4749
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4750 : Route 9 := (fun mask => (mask,id))

def c4750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4750 : Upper (D 1) (R 1) [274,36,72,130,128] 13 := by
  apply FastRouting.sound _ _ [274,36,72,130,128] 13 (by decide) (choices 1) [1,16,64] r4750 c4750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1400
  · exact u1401
  · exact u1402

def b4751 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 275 38 76 152 17 226 226 226 482), lower := (rows 275 38 76 152 17 32 64 128 256), losses := [] }

theorem u4751 : Upper (D 1) (R 1) [274,36,72,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4751
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4752 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 76 152 18 225 225 225 481), lower := (rows 275 38 76 152 18 32 64 128 256), losses := [] }

theorem u4752 : Upper (D 1) (R 1) [274,36,72,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4752
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4753 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 76 152 48 227 195 195 451), lower := (rows 275 38 76 152 48 32 64 128 256), losses := [] }

theorem u4753 : Upper (D 1) (R 1) [274,36,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4753
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4754 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 76 152 80 163 227 163 419), lower := (rows 275 38 76 152 80 32 64 128 256), losses := [] }

theorem u4754 : Upper (D 1) (R 1) [274,36,72,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4754
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4755 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 275 38 76 152 144 99 99 227 355), lower := (rows 275 38 76 152 144 32 64 128 256), losses := [] }

theorem u4755 : Upper (D 1) (R 1) [274,36,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4755
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4756 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 196 41 18 248 216 216 472), lower := (rows 275 38 196 41 18 32 64 128 256), losses := [] }

theorem u4756 : Upper (D 1) (R 1) [274,36,192,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4756
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4757 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 275 38 196 41 24 242 210 210 466), lower := (rows 275 38 196 41 24 32 64 128 256), losses := [] }

theorem u4757 : Upper (D 1) (R 1) [274,36,192,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4757
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4758 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 196 41 80 186 218 154 410), lower := (rows 275 38 196 41 80 32 64 128 256), losses := [] }

theorem u4758 : Upper (D 1) (R 1) [274,36,192,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4758
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4759 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 275 38 196 56 17 234 202 202 458), lower := (rows 275 38 196 56 17 32 64 128 256), losses := [] }

theorem u4759 : Upper (D 1) (R 1) [274,36,192,48,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4759
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4760 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 196 56 18 233 201 201 457), lower := (rows 275 38 196 56 18 32 64 128 256), losses := [] }

theorem u4760 : Upper (D 1) (R 1) [274,36,192,48,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4760
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4761 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 275 38 196 56 24 227 195 195 451), lower := (rows 275 38 196 56 24 32 64 128 256), losses := [] }

theorem u4761 : Upper (D 1) (R 1) [274,36,192,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4761
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4762 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 196 56 80 171 203 139 395), lower := (rows 275 38 196 56 80 32 64 128 256), losses := [] }

theorem u4762 : Upper (D 1) (R 1) [274,36,192,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4762
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4763 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 196 73 18 184 248 184 440), lower := (rows 275 38 196 73 18 32 64 128 256), losses := [] }

theorem u4763 : Upper (D 1) (R 1) [274,36,192,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4763
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4764 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 275 38 196 73 24 178 242 178 434), lower := (rows 275 38 196 73 24 32 64 128 256), losses := [] }

theorem u4764 : Upper (D 1) (R 1) [274,36,192,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4764
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4765 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 196 73 48 186 218 154 410), lower := (rows 275 38 196 73 48 32 64 128 256), losses := [] }

theorem u4765 : Upper (D 1) (R 1) [274,36,192,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4765
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4766 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 275 38 196 73 144 58 122 186 314), lower := (rows 275 38 196 73 144 32 64 128 256), losses := [] }

theorem u4766 : Upper (D 1) (R 1) [274,36,192,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4766
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4767 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 275 38 196 88 17 170 234 170 426), lower := (rows 275 38 196 88 17 32 64 128 256), losses := [] }

theorem u4767 : Upper (D 1) (R 1) [274,36,192,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4767
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4768 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 196 88 18 169 233 169 425), lower := (rows 275 38 196 88 18 32 64 128 256), losses := [] }

theorem u4768 : Upper (D 1) (R 1) [274,36,192,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4768
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4769 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 275 38 196 88 24 163 227 163 419), lower := (rows 275 38 196 88 24 32 64 128 256), losses := [] }

theorem u4769 : Upper (D 1) (R 1) [274,36,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4769
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4770 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 196 88 48 171 203 139 395), lower := (rows 275 38 196 88 48 32 64 128 256), losses := [] }

theorem u4770 : Upper (D 1) (R 1) [274,36,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4770
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4771 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 24, targets := 2 }], pairs := [(3,1)], upper := (rows 275 38 196 88 144 43 107 171 299), lower := (rows 275 38 196 88 144 32 64 128 256), losses := [] }

theorem u4771 : Upper (D 1) (R 1) [274,36,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4771
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4772 : PairBound 9 := { available := 154, camps := [], pairs := [], upper := (rows 275 38 196 104 17 186 218 154 410), lower := (rows 275 38 196 104 17 32 64 128 256), losses := [] }

theorem u4772 : Upper (D 1) (R 1) [274,36,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4772
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4773 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 196 104 18 185 217 153 409), lower := (rows 275 38 196 104 18 32 64 128 256), losses := [] }

theorem u4773 : Upper (D 1) (R 1) [274,36,192,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4773
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4774 : PairBound 9 := { available := 147, camps := [], pairs := [], upper := (rows 275 38 196 104 24 179 211 147 403), lower := (rows 275 38 196 104 24 32 64 128 256), losses := [] }

theorem u4774 : Upper (D 1) (R 1) [274,36,192,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4774
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4775 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 275 38 196 104 144 59 91 155 283), lower := (rows 275 38 196 104 144 32 64 128 256), losses := [] }

theorem u4775 : Upper (D 1) (R 1) [274,36,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4775
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4776 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 275 98 13 138 20 240 240 240 496), lower := (rows 275 98 13 138 20 32 64 128 256), losses := [] }

theorem u4776 : Upper (D 1) (R 1) [274,96,9,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4776
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4777 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 13 138 48 244 212 212 468), lower := (rows 275 98 13 138 48 32 64 128 256), losses := [] }

theorem u4777 : Upper (D 1) (R 1) [274,96,9,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4777
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4778 : Route 9 := (fun mask => (mask,id))

def c4778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4778 : Upper (D 1) (R 1) [274,96,9,130,128] 13 := by
  apply FastRouting.sound _ _ [274,96,9,130,128] 13 (by decide) (choices 1) [4,16,64] r4778 c4778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1403
  · exact u1404
  · exact u1405

def b4779 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 13 140 18 240 240 240 496), lower := (rows 275 98 13 140 18 32 64 128 256), losses := [] }

theorem u4779 : Upper (D 1) (R 1) [274,96,9,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4779
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4780 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 13 140 48 242 210 210 466), lower := (rows 275 98 13 140 48 32 64 128 256), losses := [] }

theorem u4780 : Upper (D 1) (R 1) [274,96,9,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4780
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4781 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 275 98 13 140 144 114 114 242 370), lower := (rows 275 98 13 140 144 32 64 128 256), losses := [] }

theorem u4781 : Upper (D 1) (R 1) [274,96,9,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4781
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4782 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 13 168 18 244 212 212 468), lower := (rows 275 98 13 168 18 32 64 128 256), losses := [] }

theorem u4782 : Upper (D 1) (R 1) [274,96,9,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4782
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4783 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 275 98 13 168 20 242 210 210 466), lower := (rows 275 98 13 168 20 32 64 128 256), losses := [] }

theorem u4783 : Upper (D 1) (R 1) [274,96,9,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4783
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4784 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 13 168 80 182 214 150 406), lower := (rows 275 98 13 168 80 32 64 128 256), losses := [] }

theorem u4784 : Upper (D 1) (R 1) [274,96,9,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4784
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4785 : Route 9 := (fun mask => (mask,id))

def c4785 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4785 : Upper (D 1) (R 1) [274,96,9,160,128] 13 := by
  apply FastRouting.sound _ _ [274,96,9,160,128] 13 (by decide) (choices 1) [2,4,16,64] r4785 c4785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1406
  · exact u1407
  · exact u1408
  · exact u1409

def b4786 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 275 98 14 137 20 240 240 240 496), lower := (rows 275 98 14 137 20 32 64 128 256), losses := [] }

theorem u4786 : Upper (D 1) (R 1) [274,96,10,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4786
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4787 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 14 137 48 244 212 212 468), lower := (rows 275 98 14 137 48 32 64 128 256), losses := [] }

theorem u4787 : Upper (D 1) (R 1) [274,96,10,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4787
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4788 : Route 9 := (fun mask => (mask,id))

def c4788 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4788 : Upper (D 1) (R 1) [274,96,10,129,128] 13 := by
  apply FastRouting.sound _ _ [274,96,10,129,128] 13 (by decide) (choices 1) [4,16,64] r4788 c4788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1410
  · exact u1411
  · exact u1412

def b4789 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 275 98 14 140 17 240 240 240 496), lower := (rows 275 98 14 140 17 32 64 128 256), losses := [] }

theorem u4789 : Upper (D 1) (R 1) [274,96,10,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4789
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4790 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 14 140 48 241 209 209 465), lower := (rows 275 98 14 140 48 32 64 128 256), losses := [] }

theorem u4790 : Upper (D 1) (R 1) [274,96,10,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4790
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4791 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 275 98 14 140 144 113 113 241 369), lower := (rows 275 98 14 140 144 32 64 128 256), losses := [] }

theorem u4791 : Upper (D 1) (R 1) [274,96,10,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4791
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4792 : PairBound 9 := { available := 228, camps := [], pairs := [], upper := (rows 275 98 14 152 17 228 228 228 484), lower := (rows 275 98 14 152 17 32 64 128 256), losses := [] }

theorem u4792 : Upper (D 1) (R 1) [274,96,10,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4792
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4793 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 275 98 14 152 20 225 225 225 481), lower := (rows 275 98 14 152 20 32 64 128 256), losses := [] }

theorem u4793 : Upper (D 1) (R 1) [274,96,10,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4793
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4794 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 14 152 48 229 197 197 453), lower := (rows 275 98 14 152 48 32 64 128 256), losses := [] }

theorem u4794 : Upper (D 1) (R 1) [274,96,10,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4794
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4795 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 275 98 14 152 144 101 101 229 357), lower := (rows 275 98 14 152 144 32 64 128 256), losses := [] }

theorem u4795 : Upper (D 1) (R 1) [274,96,10,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4795
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4796 : PairBound 9 := { available := 228, camps := [], pairs := [], upper := (rows 275 98 28 138 17 228 228 228 484), lower := (rows 275 98 28 138 17 32 64 128 256), losses := [] }

theorem u4796 : Upper (D 1) (R 1) [274,96,24,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4796
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4797 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 275 98 28 138 20 225 225 225 481), lower := (rows 275 98 28 138 20 32 64 128 256), losses := [] }

theorem u4797 : Upper (D 1) (R 1) [274,96,24,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4797
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4798 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 28 138 48 229 197 197 453), lower := (rows 275 98 28 138 48 32 64 128 256), losses := [] }

theorem u4798 : Upper (D 1) (R 1) [274,96,24,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4798
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4799 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 28 138 144 101 101 229 357), lower := (rows 275 98 28 138 144 32 64 128 256), losses := [] }

theorem u4799 : Upper (D 1) (R 1) [274,96,24,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4799
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4799
end Delivery.IrregularNine14.P01
