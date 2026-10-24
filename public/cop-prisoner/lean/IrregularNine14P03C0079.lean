import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0028
import IrregularNine14P03C0029

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4740 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 148 265 49 227 195 195 451), lower := (rows 97 14 148 265 49 32 64 128 256), losses := [] }

theorem u4740 : Upper (D 3) (R 3) [96,12,144,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4740
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4741 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 148 265 50 225 193 193 449), lower := (rows 97 14 148 265 50 32 64 128 256), losses := [] }

theorem u4741 : Upper (D 3) (R 3) [96,12,144,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4741
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4742 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 148 265 112 163 195 131 387), lower := (rows 97 14 148 265 112 32 64 128 256), losses := [] }

theorem u4742 : Upper (D 3) (R 3) [96,12,144,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4742
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4743 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 265 145 99 99 227 355), lower := (rows 97 14 148 265 145 32 64 128 256), losses := [] }

theorem u4743 : Upper (D 3) (R 3) [96,12,144,257,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4743
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4744 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 265 146 97 97 225 353), lower := (rows 97 14 148 265 146 32 64 128 256), losses := [] }

theorem u4744 : Upper (D 3) (R 3) [96,12,144,257,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4744
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4745 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 265 176 99 67 195 323), lower := (rows 97 14 148 265 176 32 64 128 256), losses := [] }

theorem u4745 : Upper (D 3) (R 3) [96,12,144,257,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4745
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4746 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 148 266 49 225 193 193 449), lower := (rows 97 14 148 266 49 32 64 128 256), losses := [] }

theorem u4746 : Upper (D 3) (R 3) [96,12,144,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4746
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4747 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 148 266 112 161 193 129 385), lower := (rows 97 14 148 266 112 32 64 128 256), losses := [] }

theorem u4747 : Upper (D 3) (R 3) [96,12,144,258,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4747
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4748 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 266 145 97 97 225 353), lower := (rows 97 14 148 266 145 32 64 128 256), losses := [] }

theorem u4748 : Upper (D 3) (R 3) [96,12,144,258,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4748
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4749 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 266 176 97 65 193 321), lower := (rows 97 14 148 266 176 32 64 128 256), losses := [] }

theorem u4749 : Upper (D 3) (R 3) [96,12,144,258,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4749
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4750 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 148 296 81 163 195 131 387), lower := (rows 97 14 148 296 81 32 64 128 256), losses := [] }

theorem u4750 : Upper (D 3) (R 3) [96,12,144,288,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4750
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4751 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 148 296 82 161 193 129 385), lower := (rows 97 14 148 296 82 32 64 128 256), losses := [] }

theorem u4751 : Upper (D 3) (R 3) [96,12,144,288,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4751
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4752 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 296 145 99 67 195 323), lower := (rows 97 14 148 296 145 32 64 128 256), losses := [] }

theorem u4752 : Upper (D 3) (R 3) [96,12,144,288,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4752
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4753 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 296 146 97 65 193 321), lower := (rows 97 14 148 296 146 32 64 128 256), losses := [] }

theorem u4753 : Upper (D 3) (R 3) [96,12,144,288,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4753
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4754 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 296 208 35 67 131 259), lower := (rows 97 14 148 296 208 32 64 128 256), losses := [] }

theorem u4754 : Upper (D 3) (R 3) [96,12,144,288,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4754
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4755 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 392 50 97 65 193 321), lower := (rows 97 14 148 392 50 32 64 128 256), losses := [] }

theorem u4755 : Upper (D 3) (R 3) [96,12,144,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4755
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4756 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 200 273 51 83 147 275), lower := (rows 97 14 164 200 273 32 64 128 256), losses := [] }

theorem u4756 : Upper (D 3) (R 3) [96,12,160,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4756
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4757 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 200 274 49 81 145 273), lower := (rows 97 14 164 200 274 32 64 128 256), losses := [] }

theorem u4757 : Upper (D 3) (R 3) [96,12,160,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4757
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4758 : PairBound 9 := { available := 147, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 164 265 81 179 211 147 403), lower := (rows 97 14 164 265 81 32 64 128 256), losses := [] }

theorem u4758 : Upper (D 3) (R 3) [96,12,160,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4758
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4759 : Route 9 := (fun mask => (mask,id))

def c4759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4759 : Upper (D 3) (R 3) [96,12,160,257,66] 13 := by
  apply FastRouting.sound _ _ [96,12,160,257,66] 13 (by decide) (choices 1) [1,16,128] r4759 c4759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1733
  · exact u1734
  · exact u1735

def r4760 : Route 9 := (fun mask => (mask,id))

def c4760 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4760 : Upper (D 3) (R 3) [96,12,160,257,129] 13 := by
  apply FastRouting.sound _ _ [96,12,160,257,129] 13 (by decide) (choices 1) [1,2,16,64] r4760 c4760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1736
  · exact u1737
  · exact u1738
  · exact u1739

def b4761 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 265 146 113 81 209 337), lower := (rows 97 14 164 265 146 32 64 128 256), losses := [] }

theorem u4761 : Upper (D 3) (R 3) [96,12,160,257,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4761
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4762 : Route 9 := (fun mask => (mask,id))

def c4762 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4762 : Upper (D 3) (R 3) [96,12,160,257,192] 13 := by
  apply FastRouting.sound _ _ [96,12,160,257,192] 13 (by decide) (choices 1) [1,2,16] r4762 c4762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1740
  · exact u1741
  · exact u1742

def b4763 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 164 266 145 113 81 209 337), lower := (rows 97 14 164 266 145 32 64 128 256), losses := [] }

theorem u4763 : Upper (D 3) (R 3) [96,12,160,258,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4763
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4764 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 164 266 208 49 81 145 273), lower := (rows 97 14 164 266 208 32 64 128 256), losses := [] }

theorem u4764 : Upper (D 3) (R 3) [96,12,160,258,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4764
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4765 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 164 280 81 163 195 131 387), lower := (rows 97 14 164 280 81 32 64 128 256), losses := [] }

theorem u4765 : Upper (D 3) (R 3) [96,12,160,272,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4765
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4766 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 164 280 82 161 193 129 385), lower := (rows 97 14 164 280 82 32 64 128 256), losses := [] }

theorem u4766 : Upper (D 3) (R 3) [96,12,160,272,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4766
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4767 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 280 145 99 67 195 323), lower := (rows 97 14 164 280 145 32 64 128 256), losses := [] }

theorem u4767 : Upper (D 3) (R 3) [96,12,160,272,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4767
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4768 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 280 146 97 65 193 321), lower := (rows 97 14 164 280 146 32 64 128 256), losses := [] }

theorem u4768 : Upper (D 3) (R 3) [96,12,160,272,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4768
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4769 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 280 208 35 67 131 259), lower := (rows 97 14 164 280 208 32 64 128 256), losses := [] }

theorem u4769 : Upper (D 3) (R 3) [96,12,160,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4769
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4770 : Route 9 := (fun mask => (mask,id))

def c4770 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4770 : Upper (D 3) (R 3) [96,12,160,320,129] 13 := by
  apply FastRouting.sound _ _ [96,12,160,320,129] 13 (by decide) (choices 1) [1,2,16] r4770 c4770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1743
  · exact u1744
  · exact u1745

def b4771 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 328 146 49 81 145 273), lower := (rows 97 14 164 328 146 32 64 128 256), losses := [] }

theorem u4771 : Upper (D 3) (R 3) [96,12,160,320,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4771
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4772 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 392 82 49 81 145 273), lower := (rows 97 14 164 392 82 32 64 128 256), losses := [] }

theorem u4772 : Upper (D 3) (R 3) [96,12,160,384,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4772
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4773 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 70 137 148 313 345 409 281), lower := (rows 97 35 70 137 148 32 64 128 256), losses := [] }

theorem u4773 : Upper (D 3) (R 3) [96,33,66,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4773
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4774 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 70 137 273 188 220 156 412), lower := (rows 97 35 70 137 273 32 64 128 256), losses := [] }

theorem u4774 : Upper (D 3) (R 3) [96,33,66,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4774
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4775 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 70 137 276 185 217 153 409), lower := (rows 97 35 70 137 276 32 64 128 256), losses := [] }

theorem u4775 : Upper (D 3) (R 3) [96,33,66,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4775
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4776 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 70 137 280 181 213 149 405), lower := (rows 97 35 70 137 280 32 64 128 256), losses := [] }

theorem u4776 : Upper (D 3) (R 3) [96,33,66,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4776
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4777 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 70 137 400 61 93 157 285), lower := (rows 97 35 70 137 400 32 64 128 256), losses := [] }

theorem u4777 : Upper (D 3) (R 3) [96,33,66,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4777
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4778 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 70 140 273 185 217 153 409), lower := (rows 97 35 70 140 273 32 64 128 256), losses := [] }

theorem u4778 : Upper (D 3) (R 3) [96,33,66,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4778
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4779 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 70 140 280 177 209 145 401), lower := (rows 97 35 70 140 280 32 64 128 256), losses := [] }

theorem u4779 : Upper (D 3) (R 3) [96,33,66,132,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4779
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4780 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 70 140 400 57 89 153 281), lower := (rows 97 35 70 140 400 32 64 128 256), losses := [] }

theorem u4780 : Upper (D 3) (R 3) [96,33,66,132,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4780
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4781 : PairBound 9 := { available := 141, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 70 152 273 173 205 141 397), lower := (rows 97 35 70 152 273 32 64 128 256), losses := [] }

theorem u4781 : Upper (D 3) (R 3) [96,33,66,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4781
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4782 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 70 152 276 169 201 137 393), lower := (rows 97 35 70 152 276 32 64 128 256), losses := [] }

theorem u4782 : Upper (D 3) (R 3) [96,33,66,144,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4782
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4783 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 70 152 280 165 197 133 389), lower := (rows 97 35 70 152 280 32 64 128 256), losses := [] }

theorem u4783 : Upper (D 3) (R 3) [96,33,66,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4783
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4784 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 137 146 309 341 405 277), lower := (rows 97 35 76 137 146 32 64 128 256), losses := [] }

theorem u4784 : Upper (D 3) (R 3) [96,33,72,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4784
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4785 : PairBound 9 := { available := 150, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 137 273 182 214 150 406), lower := (rows 97 35 76 137 273 32 64 128 256), losses := [] }

theorem u4785 : Upper (D 3) (R 3) [96,33,72,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4785
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4786 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 137 274 181 213 149 405), lower := (rows 97 35 76 137 274 32 64 128 256), losses := [] }

theorem u4786 : Upper (D 3) (R 3) [96,33,72,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4786
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4787 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 137 276 179 211 147 403), lower := (rows 97 35 76 137 276 32 64 128 256), losses := [] }

theorem u4787 : Upper (D 3) (R 3) [96,33,72,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4787
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4788 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 137 400 55 87 151 279), lower := (rows 97 35 76 137 400 32 64 128 256), losses := [] }

theorem u4788 : Upper (D 3) (R 3) [96,33,72,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4788
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4789 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 138 145 309 341 405 277), lower := (rows 97 35 76 138 145 32 64 128 256), losses := [] }

theorem u4789 : Upper (D 3) (R 3) [96,33,72,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4789
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4790 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 138 273 181 213 149 405), lower := (rows 97 35 76 138 273 32 64 128 256), losses := [] }

theorem u4790 : Upper (D 3) (R 3) [96,33,72,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4790
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4791 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 138 276 177 209 145 401), lower := (rows 97 35 76 138 276 32 64 128 256), losses := [] }

theorem u4791 : Upper (D 3) (R 3) [96,33,72,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4791
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4792 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 138 400 53 85 149 277), lower := (rows 97 35 76 138 400 32 64 128 256), losses := [] }

theorem u4792 : Upper (D 3) (R 3) [96,33,72,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4792
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4793 : PairBound 9 := { available := 135, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 152 273 167 199 135 391), lower := (rows 97 35 76 152 273 32 64 128 256), losses := [] }

theorem u4793 : Upper (D 3) (R 3) [96,33,72,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4793
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4794 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 152 274 165 197 133 389), lower := (rows 97 35 76 152 274 32 64 128 256), losses := [] }

theorem u4794 : Upper (D 3) (R 3) [96,33,72,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4794
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4795 : PairBound 9 := { available := 150, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 265 145 182 214 150 406), lower := (rows 97 35 76 265 145 32 64 128 256), losses := [] }

theorem u4795 : Upper (D 3) (R 3) [96,33,72,257,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4795
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4796 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 265 146 181 213 149 405), lower := (rows 97 35 76 265 146 32 64 128 256), losses := [] }

theorem u4796 : Upper (D 3) (R 3) [96,33,72,257,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4796
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4797 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 265 148 179 211 147 403), lower := (rows 97 35 76 265 148 32 64 128 256), losses := [] }

theorem u4797 : Upper (D 3) (R 3) [96,33,72,257,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4797
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4798 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 266 145 181 213 149 405), lower := (rows 97 35 76 266 145 32 64 128 256), losses := [] }

theorem u4798 : Upper (D 3) (R 3) [96,33,72,258,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4798
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4799 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 266 148 177 209 145 401), lower := (rows 97 35 76 266 148 32 64 128 256), losses := [] }

theorem u4799 : Upper (D 3) (R 3) [96,33,72,258,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4799
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4799
end Delivery.IrregularNine14.P03
