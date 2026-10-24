import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0029

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4800 : PairBound 9 := { available := 135, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 280 145 167 199 135 391), lower := (rows 97 35 76 280 145 32 64 128 256), losses := [] }

theorem u4800 : Upper (D 3) (R 3) [96,33,72,272,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4800
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4801 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 280 146 165 197 133 389), lower := (rows 97 35 76 280 146 32 64 128 256), losses := [] }

theorem u4801 : Upper (D 3) (R 3) [96,33,72,272,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4801
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4802 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 392 145 55 87 151 279), lower := (rows 97 35 76 392 145 32 64 128 256), losses := [] }

theorem u4802 : Upper (D 3) (R 3) [96,33,72,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4802
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4803 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 76 392 146 53 85 149 277), lower := (rows 97 35 76 392 146 32 64 128 256), losses := [] }

theorem u4803 : Upper (D 3) (R 3) [96,33,72,384,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4803
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4804 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 138 273 124 92 220 348), lower := (rows 97 35 133 138 273 32 64 128 256), losses := [] }

theorem u4804 : Upper (D 3) (R 3) [96,33,129,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4804
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4805 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 138 276 121 89 217 345), lower := (rows 97 35 133 138 276 32 64 128 256), losses := [] }

theorem u4805 : Upper (D 3) (R 3) [96,33,129,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4805
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4806 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 138 280 117 85 213 341), lower := (rows 97 35 133 138 280 32 64 128 256), losses := [] }

theorem u4806 : Upper (D 3) (R 3) [96,33,129,130,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4806
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4807 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 138 336 61 93 157 285), lower := (rows 97 35 133 138 336 32 64 128 256), losses := [] }

theorem u4807 : Upper (D 3) (R 3) [96,33,129,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4807
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4808 : PairBound 9 := { available := 78, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 152 273 110 78 206 334), lower := (rows 97 35 133 152 273 32 64 128 256), losses := [] }

theorem u4808 : Upper (D 3) (R 3) [96,33,129,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4808
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4809 : PairBound 9 := { available := 77, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 152 274 109 77 205 333), lower := (rows 97 35 133 152 274 32 64 128 256), losses := [] }

theorem u4809 : Upper (D 3) (R 3) [96,33,129,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4809
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4810 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 152 336 47 79 143 271), lower := (rows 97 35 133 152 336 32 64 128 256), losses := [] }

theorem u4810 : Upper (D 3) (R 3) [96,33,129,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4810
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4811 : PairBound 9 := { available := 30, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 200 273 62 94 158 286), lower := (rows 97 35 133 200 273 32 64 128 256), losses := [] }

theorem u4811 : Upper (D 3) (R 3) [96,33,129,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4811
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4812 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 200 274 61 93 157 285), lower := (rows 97 35 133 200 274 32 64 128 256), losses := [] }

theorem u4812 : Upper (D 3) (R 3) [96,33,129,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4812
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4813 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 200 276 59 91 155 283), lower := (rows 97 35 133 200 276 32 64 128 256), losses := [] }

theorem u4813 : Upper (D 3) (R 3) [96,33,129,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4813
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4814 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 200 280 55 87 151 279), lower := (rows 97 35 133 200 280 32 64 128 256), losses := [] }

theorem u4814 : Upper (D 3) (R 3) [96,33,129,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4814
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4815 : PairBound 9 := { available := 77, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 134 152 273 109 77 205 333), lower := (rows 97 35 134 152 273 32 64 128 256), losses := [] }

theorem u4815 : Upper (D 3) (R 3) [96,33,130,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4815
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4816 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 134 152 336 45 77 141 269), lower := (rows 97 35 134 152 336 32 64 128 256), losses := [] }

theorem u4816 : Upper (D 3) (R 3) [96,33,130,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4816
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4817 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 134 200 273 61 93 157 285), lower := (rows 97 35 134 200 273 32 64 128 256), losses := [] }

theorem u4817 : Upper (D 3) (R 3) [96,33,130,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4817
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4818 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 134 200 276 57 89 153 281), lower := (rows 97 35 134 200 276 32 64 128 256), losses := [] }

theorem u4818 : Upper (D 3) (R 3) [96,33,130,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4818
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4819 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 134 200 280 53 85 149 277), lower := (rows 97 35 134 200 280 32 64 128 256), losses := [] }

theorem u4819 : Upper (D 3) (R 3) [96,33,130,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4819
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4820 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 140 265 208 55 87 151 279), lower := (rows 97 35 140 265 208 32 64 128 256), losses := [] }

theorem u4820 : Upper (D 3) (R 3) [96,33,136,257,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4820
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4821 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 140 266 208 53 85 149 277), lower := (rows 97 35 140 266 208 32 64 128 256), losses := [] }

theorem u4821 : Upper (D 3) (R 3) [96,33,136,258,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4821
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4822 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 137 273 185 217 153 409), lower := (rows 97 38 70 137 273 32 64 128 256), losses := [] }

theorem u4822 : Upper (D 3) (R 3) [96,36,66,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4822
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4823 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 137 280 177 209 145 401), lower := (rows 97 38 70 137 280 32 64 128 256), losses := [] }

theorem u4823 : Upper (D 3) (R 3) [96,36,66,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4823
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4824 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 137 400 57 89 153 281), lower := (rows 97 38 70 137 400 32 64 128 256), losses := [] }

theorem u4824 : Upper (D 3) (R 3) [96,36,66,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4824
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4825 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 152 273 169 201 137 393), lower := (rows 97 38 70 152 273 32 64 128 256), losses := [] }

theorem u4825 : Upper (D 3) (R 3) [96,36,66,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4825
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4826 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 152 280 161 193 129 385), lower := (rows 97 38 70 152 280 32 64 128 256), losses := [] }

theorem u4826 : Upper (D 3) (R 3) [96,36,66,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4826
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4827 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 76 137 145 307 339 403 275), lower := (rows 97 38 76 137 145 32 64 128 256), losses := [] }

theorem u4827 : Upper (D 3) (R 3) [96,36,72,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4827
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4828 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 137 146 305 337 401 273), lower := (rows 97 38 76 137 146 32 64 128 256), losses := [] }

theorem u4828 : Upper (D 3) (R 3) [96,36,72,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4828
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4829 : Route 9 := (fun mask => (mask,id))

def c4829 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4829 : Upper (D 3) (R 3) [96,36,72,129,257] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,257] 13 (by decide) (choices 1) [1,2,16,128] r4829 c4829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1746
  · exact u1747
  · exact u1748
  · exact u1749

def r4830 : Route 9 := (fun mask => (mask,id))

def c4830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4830 : Upper (D 3) (R 3) [96,36,72,129,258] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,258] 13 (by decide) (choices 1) [1,16,128] r4830 c4830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1750
  · exact u1751
  · exact u1752

def r4831 : Route 9 := (fun mask => (mask,id))

def c4831 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4831 : Upper (D 3) (R 3) [96,36,72,129,384] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,384] 13 (by decide) (choices 1) [1,2,16] r4831 c4831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1753
  · exact u1754
  · exact u1755

def b4832 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 76 138 145 305 337 401 273), lower := (rows 97 38 76 138 145 32 64 128 256), losses := [] }

theorem u4832 : Upper (D 3) (R 3) [96,36,72,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4832
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4833 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 76 138 273 177 209 145 401), lower := (rows 97 38 76 138 273 32 64 128 256), losses := [] }

theorem u4833 : Upper (D 3) (R 3) [96,36,72,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4833
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4834 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 76 138 400 49 81 145 273), lower := (rows 97 38 76 138 400 32 64 128 256), losses := [] }

theorem u4834 : Upper (D 3) (R 3) [96,36,72,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4834
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4835 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 145 291 323 387 259), lower := (rows 97 38 76 152 145 32 64 128 256), losses := [] }

theorem u4835 : Upper (D 3) (R 3) [96,36,72,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4835
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4836 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 146 289 321 385 257), lower := (rows 97 38 76 152 146 32 64 128 256), losses := [] }

theorem u4836 : Upper (D 3) (R 3) [96,36,72,144,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4836
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4837 : Route 9 := (fun mask => (mask,id))

def c4837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4837 : Upper (D 3) (R 3) [96,36,72,144,257] 13 := by
  apply FastRouting.sound _ _ [96,36,72,144,257] 13 (by decide) (choices 1) [1,2,128] r4837 c4837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1756
  · exact u1757
  · exact u1758

def r4838 : Route 9 := (fun mask => (mask,id))

def c4838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4838 : Upper (D 3) (R 3) [96,36,72,144,258] 13 := by
  apply FastRouting.sound _ _ [96,36,72,144,258] 13 (by decide) (choices 1) [1,128] r4838 c4838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1759
  · exact u1760

def b4839 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 400 35 67 131 259), lower := (rows 97 38 76 152 400 32 64 128 256), losses := [] }

theorem u4839 : Upper (D 3) (R 3) [96,36,72,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4839
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4840 : Route 9 := (fun mask => (mask,id))

def c4840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4840 : Upper (D 3) (R 3) [96,36,72,257,129] 13 := by
  apply FastRouting.sound _ _ [96,36,72,257,129] 13 (by decide) (choices 1) [1,2,16,128] r4840 c4840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1761
  · exact u1762
  · exact u1763
  · exact u1764

def r4841 : Route 9 := (fun mask => (mask,id))

def c4841 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4841 : Upper (D 3) (R 3) [96,36,72,257,130] 13 := by
  apply FastRouting.sound _ _ [96,36,72,257,130] 13 (by decide) (choices 1) [1,16,128] r4841 c4841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1765
  · exact u1766
  · exact u1767

def b4842 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 76 266 145 177 209 145 401), lower := (rows 97 38 76 266 145 32 64 128 256), losses := [] }

theorem u4842 : Upper (D 3) (R 3) [96,36,72,258,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4842
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4843 : Route 9 := (fun mask => (mask,id))

def c4843 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4843 : Upper (D 3) (R 3) [96,36,72,272,129] 13 := by
  apply FastRouting.sound _ _ [96,36,72,272,129] 13 (by decide) (choices 1) [1,2,128] r4843 c4843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1768
  · exact u1769
  · exact u1770

def r4844 : Route 9 := (fun mask => (mask,id))

def c4844 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4844 : Upper (D 3) (R 3) [96,36,72,272,130] 13 := by
  apply FastRouting.sound _ _ [96,36,72,272,130] 13 (by decide) (choices 1) [1,128] r4844 c4844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1771
  · exact u1772

def r4845 : Route 9 := (fun mask => (mask,id))

def c4845 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4845 : Upper (D 3) (R 3) [96,36,72,384,129] 13 := by
  apply FastRouting.sound _ _ [96,36,72,384,129] 13 (by decide) (choices 1) [1,2,16] r4845 c4845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1773
  · exact u1774
  · exact u1775

def b4846 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 392 146 49 81 145 273), lower := (rows 97 38 76 392 146 32 64 128 256), losses := [] }

theorem u4846 : Upper (D 3) (R 3) [96,36,72,384,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4846
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4847 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 133 88 145 299 331 395 267), lower := (rows 97 38 133 88 145 32 64 128 256), losses := [] }

theorem u4847 : Upper (D 3) (R 3) [96,36,129,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4847
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4848 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 88 146 297 329 393 265), lower := (rows 97 38 133 88 146 32 64 128 256), losses := [] }

theorem u4848 : Upper (D 3) (R 3) [96,36,129,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4848
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4849 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 88 152 291 323 387 259), lower := (rows 97 38 133 88 152 32 64 128 256), losses := [] }

theorem u4849 : Upper (D 3) (R 3) [96,36,129,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4849
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4850 : Route 9 := (fun mask => (mask,id))

def c4850 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4850 : Upper (D 3) (R 3) [96,36,129,80,257] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,257] 13 (by decide) (choices 1) [1,2,8,128] r4850 c4850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1776
  · exact u1777
  · exact u1778
  · exact u1779

def r4851 : Route 9 := (fun mask => (mask,id))

def c4851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4851 : Upper (D 3) (R 3) [96,36,129,80,258] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,258] 13 (by decide) (choices 1) [1,8,128] r4851 c4851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1780
  · exact u1781
  · exact u1782

def b4852 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 88 280 163 195 131 387), lower := (rows 97 38 133 88 280 32 64 128 256), losses := [] }

theorem u4852 : Upper (D 3) (R 3) [96,36,129,80,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4852
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4853 : Route 9 := (fun mask => (mask,id))

def c4853 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4853 : Upper (D 3) (R 3) [96,36,129,80,384] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,384] 13 (by decide) (choices 1) [1,2,8] r4853 c4853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1783
  · exact u1784
  · exact u1785

def b4854 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 133 137 273 122 90 218 346), lower := (rows 97 38 133 137 273 32 64 128 256), losses := [] }

theorem u4854 : Upper (D 3) (R 3) [96,36,129,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4854
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4855 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 133 137 274 121 89 217 345), lower := (rows 97 38 133 137 274 32 64 128 256), losses := [] }

theorem u4855 : Upper (D 3) (R 3) [96,36,129,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4855
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4856 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 133 137 280 115 83 211 339), lower := (rows 97 38 133 137 280 32 64 128 256), losses := [] }

theorem u4856 : Upper (D 3) (R 3) [96,36,129,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4856
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4857 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 133 137 336 59 91 155 283), lower := (rows 97 38 133 137 336 32 64 128 256), losses := [] }

theorem u4857 : Upper (D 3) (R 3) [96,36,129,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4857
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4858 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 138 273 121 89 217 345), lower := (rows 97 38 133 138 273 32 64 128 256), losses := [] }

theorem u4858 : Upper (D 3) (R 3) [96,36,129,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4858
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4859 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 138 280 113 81 209 337), lower := (rows 97 38 133 138 280 32 64 128 256), losses := [] }

theorem u4859 : Upper (D 3) (R 3) [96,36,129,130,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4859
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4859
end Delivery.IrregularNine14.P03
