import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0029
import IrregularNine14P03C0030

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4860 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 138 336 57 89 153 281), lower := (rows 97 38 133 138 336 32 64 128 256), losses := [] }

theorem u4860 : Upper (D 3) (R 3) [96,36,129,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4860
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4861 : Route 9 := (fun mask => (mask,id))

def c4861 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4861 : Upper (D 3) (R 3) [96,36,129,144,257] 13 := by
  apply FastRouting.sound _ _ [96,36,129,144,257] 13 (by decide) (choices 1) [1,2,8,64] r4861 c4861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1786
  · exact u1787
  · exact u1788
  · exact u1789

def b4862 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 152 274 105 73 201 329), lower := (rows 97 38 133 152 274 32 64 128 256), losses := [] }

theorem u4862 : Upper (D 3) (R 3) [96,36,129,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4862
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4863 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 152 280 99 67 195 323), lower := (rows 97 38 133 152 280 32 64 128 256), losses := [] }

theorem u4863 : Upper (D 3) (R 3) [96,36,129,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4863
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4864 : Route 9 := (fun mask => (mask,id))

def c4864 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4864 : Upper (D 3) (R 3) [96,36,129,144,320] 13 := by
  apply FastRouting.sound _ _ [96,36,129,144,320] 13 (by decide) (choices 1) [1,2,8] r4864 c4864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1790
  · exact u1791
  · exact u1792

def r4865 : Route 9 := (fun mask => (mask,id))

def c4865 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4865 : Upper (D 3) (R 3) [96,36,129,192,257] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,257] 13 (by decide) (choices 1) [1,2,8,16] r4865 c4865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1793
  · exact u1794
  · exact u1795
  · exact u1796

def r4866 : Route 9 := (fun mask => (mask,id))

def c4866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4866 : Upper (D 3) (R 3) [96,36,129,192,258] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,258] 13 (by decide) (choices 1) [1,8,16] r4866 c4866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1797
  · exact u1798
  · exact u1799

def r4867 : Route 9 := (fun mask => (mask,id))

def c4867 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4867 : Upper (D 3) (R 3) [96,36,129,192,264] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,264] 13 (by decide) (choices 1) [1,2,16] r4867 c4867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1800
  · exact u1801
  · exact u1802

def b4868 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 88 273 169 201 137 393), lower := (rows 97 38 134 88 273 32 64 128 256), losses := [] }

theorem u4868 : Upper (D 3) (R 3) [96,36,130,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4868
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4869 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 88 400 41 73 137 265), lower := (rows 97 38 134 88 400 32 64 128 256), losses := [] }

theorem u4869 : Upper (D 3) (R 3) [96,36,130,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4869
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4870 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 137 273 121 89 217 345), lower := (rows 97 38 134 137 273 32 64 128 256), losses := [] }

theorem u4870 : Upper (D 3) (R 3) [96,36,130,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4870
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4871 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 137 280 113 81 209 337), lower := (rows 97 38 134 137 280 32 64 128 256), losses := [] }

theorem u4871 : Upper (D 3) (R 3) [96,36,130,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4871
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4872 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 137 336 57 89 153 281), lower := (rows 97 38 134 137 336 32 64 128 256), losses := [] }

theorem u4872 : Upper (D 3) (R 3) [96,36,130,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4872
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4873 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 152 273 105 73 201 329), lower := (rows 97 38 134 152 273 32 64 128 256), losses := [] }

theorem u4873 : Upper (D 3) (R 3) [96,36,130,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4873
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4874 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 152 280 97 65 193 321), lower := (rows 97 38 134 152 280 32 64 128 256), losses := [] }

theorem u4874 : Upper (D 3) (R 3) [96,36,130,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4874
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4875 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 152 336 41 73 137 265), lower := (rows 97 38 134 152 336 32 64 128 256), losses := [] }

theorem u4875 : Upper (D 3) (R 3) [96,36,130,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4875
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4876 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 200 273 57 89 153 281), lower := (rows 97 38 134 200 273 32 64 128 256), losses := [] }

theorem u4876 : Upper (D 3) (R 3) [96,36,130,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4876
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4877 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 200 280 49 81 145 273), lower := (rows 97 38 134 200 280 32 64 128 256), losses := [] }

theorem u4877 : Upper (D 3) (R 3) [96,36,130,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4877
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4878 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 146 289 321 385 257), lower := (rows 97 38 140 88 146 32 64 128 256), losses := [] }

theorem u4878 : Upper (D 3) (R 3) [96,36,136,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4878
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4879 : Route 9 := (fun mask => (mask,id))

def c4879 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4879 : Upper (D 3) (R 3) [96,36,136,80,257] 13 := by
  apply FastRouting.sound _ _ [96,36,136,80,257] 13 (by decide) (choices 1) [1,2,128] r4879 c4879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1803
  · exact u1804
  · exact u1805

def r4880 : Route 9 := (fun mask => (mask,id))

def c4880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4880 : Upper (D 3) (R 3) [96,36,136,80,258] 13 := by
  apply FastRouting.sound _ _ [96,36,136,80,258] 13 (by decide) (choices 1) [1,128] r4880 c4880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1806
  · exact u1807

def b4881 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 400 35 67 131 259), lower := (rows 97 38 140 88 400 32 64 128 256), losses := [] }

theorem u4881 : Upper (D 3) (R 3) [96,36,136,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4881
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4882 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 137 273 115 83 211 339), lower := (rows 97 38 140 137 273 32 64 128 256), losses := [] }

theorem u4882 : Upper (D 3) (R 3) [96,36,136,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4882
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4883 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 137 274 113 81 209 337), lower := (rows 97 38 140 137 274 32 64 128 256), losses := [] }

theorem u4883 : Upper (D 3) (R 3) [96,36,136,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4883
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4884 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 137 336 51 83 147 275), lower := (rows 97 38 140 137 336 32 64 128 256), losses := [] }

theorem u4884 : Upper (D 3) (R 3) [96,36,136,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4884
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4885 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 138 273 113 81 209 337), lower := (rows 97 38 140 138 273 32 64 128 256), losses := [] }

theorem u4885 : Upper (D 3) (R 3) [96,36,136,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4885
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4886 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 138 336 49 81 145 273), lower := (rows 97 38 140 138 336 32 64 128 256), losses := [] }

theorem u4886 : Upper (D 3) (R 3) [96,36,136,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4886
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4887 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 152 273 99 67 195 323), lower := (rows 97 38 140 152 273 32 64 128 256), losses := [] }

theorem u4887 : Upper (D 3) (R 3) [96,36,136,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4887
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4888 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 152 274 97 65 193 321), lower := (rows 97 38 140 152 274 32 64 128 256), losses := [] }

theorem u4888 : Upper (D 3) (R 3) [96,36,136,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4888
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4889 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 152 336 35 67 131 259), lower := (rows 97 38 140 152 336 32 64 128 256), losses := [] }

theorem u4889 : Upper (D 3) (R 3) [96,36,136,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4889
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4890 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 200 273 51 83 147 275), lower := (rows 97 38 140 200 273 32 64 128 256), losses := [] }

theorem u4890 : Upper (D 3) (R 3) [96,36,136,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4890
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4891 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 200 274 49 81 145 273), lower := (rows 97 38 140 200 274 32 64 128 256), losses := [] }

theorem u4891 : Upper (D 3) (R 3) [96,36,136,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4891
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4892 : Route 9 := (fun mask => (mask,id))

def c4892 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4892 : Upper (D 3) (R 3) [96,36,136,257,129] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,129] 13 (by decide) (choices 1) [1,2,16,64] r4892 c4892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1808
  · exact u1809
  · exact u1810
  · exact u1811

def b4893 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 265 146 113 81 209 337), lower := (rows 97 38 140 265 146 32 64 128 256), losses := [] }

theorem u4893 : Upper (D 3) (R 3) [96,36,136,257,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4893
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4894 : Route 9 := (fun mask => (mask,id))

def c4894 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4894 : Upper (D 3) (R 3) [96,36,136,257,192] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,192] 13 (by decide) (choices 1) [1,2,16] r4894 c4894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1812
  · exact u1813
  · exact u1814

def b4895 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 140 266 145 113 81 209 337), lower := (rows 97 38 140 266 145 32 64 128 256), losses := [] }

theorem u4895 : Upper (D 3) (R 3) [96,36,136,258,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4895
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4896 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 140 266 208 49 81 145 273), lower := (rows 97 38 140 266 208 32 64 128 256), losses := [] }

theorem u4896 : Upper (D 3) (R 3) [96,36,136,258,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4896
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4897 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 280 145 99 67 195 323), lower := (rows 97 38 140 280 145 32 64 128 256), losses := [] }

theorem u4897 : Upper (D 3) (R 3) [96,36,136,272,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4897
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4898 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 280 146 97 65 193 321), lower := (rows 97 38 140 280 146 32 64 128 256), losses := [] }

theorem u4898 : Upper (D 3) (R 3) [96,36,136,272,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4898
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4899 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 280 208 35 67 131 259), lower := (rows 97 38 140 280 208 32 64 128 256), losses := [] }

theorem u4899 : Upper (D 3) (R 3) [96,36,136,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4899
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4900 : Route 9 := (fun mask => (mask,id))

def c4900 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4900 : Upper (D 3) (R 3) [96,36,136,320,129] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320,129] 13 (by decide) (choices 1) [1,2,16] r4900 c4900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1815
  · exact u1816
  · exact u1817

def b4901 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 328 146 49 81 145 273), lower := (rows 97 38 140 328 146 32 64 128 256), losses := [] }

theorem u4901 : Upper (D 3) (R 3) [96,36,136,320,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4901
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4902 : Route 9 := (fun mask => (mask,id))

def c4902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4902 : Upper (D 3) (R 3) [96,36,192,129,257] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,257] 13 (by decide) (choices 1) [1,2,8,16] r4902 c4902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1818
  · exact u1819
  · exact u1820
  · exact u1821

def r4903 : Route 9 := (fun mask => (mask,id))

def c4903 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4903 : Upper (D 3) (R 3) [96,36,192,129,258] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,258] 13 (by decide) (choices 1) [1,8,16] r4903 c4903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1822
  · exact u1823
  · exact u1824

def r4904 : Route 9 := (fun mask => (mask,id))

def c4904 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4904 : Upper (D 3) (R 3) [96,36,192,129,264] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,264] 13 (by decide) (choices 1) [1,2,16] r4904 c4904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1825
  · exact u1826
  · exact u1827

def b4905 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 138 273 57 89 153 281), lower := (rows 97 38 196 138 273 32 64 128 256), losses := [] }

theorem u4905 : Upper (D 3) (R 3) [96,36,192,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4905
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4906 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 138 280 49 81 145 273), lower := (rows 97 38 196 138 280 32 64 128 256), losses := [] }

theorem u4906 : Upper (D 3) (R 3) [96,36,192,130,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4906
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4907 : Route 9 := (fun mask => (mask,id))

def c4907 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4907 : Upper (D 3) (R 3) [96,36,192,144,257] 13 := by
  apply FastRouting.sound _ _ [96,36,192,144,257] 13 (by decide) (choices 1) [1,2,8] r4907 c4907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1828
  · exact u1829
  · exact u1830

def b4908 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 152 274 41 73 137 265), lower := (rows 97 38 196 152 274 32 64 128 256), losses := [] }

theorem u4908 : Upper (D 3) (R 3) [96,36,192,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4908
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4909 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 152 280 35 67 131 259), lower := (rows 97 38 196 152 280 32 64 128 256), losses := [] }

theorem u4909 : Upper (D 3) (R 3) [96,36,192,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4909
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4910 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 261 137 145 122 90 218 346), lower := (rows 97 38 261 137 145 32 64 128 256), losses := [] }

theorem u4910 : Upper (D 3) (R 3) [96,36,257,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4910
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4911 : Route 9 := (fun mask => (mask,id))

def c4911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4911 : Upper (D 3) (R 3) [96,36,257,129,130] 13 := by
  apply FastRouting.sound _ _ [96,36,257,129,130] 13 (by decide) (choices 1) [1,8,16,64] r4911 c4911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1831
  · exact u1832
  · exact u1833
  · exact u1834

def b4912 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 261 137 152 115 83 211 339), lower := (rows 97 38 261 137 152 32 64 128 256), losses := [] }

theorem u4912 : Upper (D 3) (R 3) [96,36,257,129,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4912
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4913 : Route 9 := (fun mask => (mask,id))

def c4913 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4913 : Upper (D 3) (R 3) [96,36,257,129,192] 13 := by
  apply FastRouting.sound _ _ [96,36,257,129,192] 13 (by decide) (choices 1) [1,2,8,16] r4913 c4913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1835
  · exact u1836
  · exact u1837
  · exact u1838

def b4914 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 261 138 152 113 81 209 337), lower := (rows 97 38 261 138 152 32 64 128 256), losses := [] }

theorem u4914 : Upper (D 3) (R 3) [96,36,257,130,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4914
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4915 : Route 9 := (fun mask => (mask,id))

def c4915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4915 : Upper (D 3) (R 3) [96,36,257,130,192] 13 := by
  apply FastRouting.sound _ _ [96,36,257,130,192] 13 (by decide) (choices 1) [1,8,16] r4915 c4915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1839
  · exact u1840
  · exact u1841

def b4916 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 261 152 152 99 67 195 323), lower := (rows 97 38 261 152 152 32 64 128 256), losses := [] }

theorem u4916 : Upper (D 3) (R 3) [96,36,257,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4916
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4917 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 261 152 208 43 75 139 267), lower := (rows 97 38 261 152 208 32 64 128 256), losses := [] }

theorem u4917 : Upper (D 3) (R 3) [96,36,257,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4917
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4918 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 262 137 208 57 89 153 281), lower := (rows 97 38 262 137 208 32 64 128 256), losses := [] }

theorem u4918 : Upper (D 3) (R 3) [96,36,258,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4918
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4919 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 268 137 145 115 83 211 339), lower := (rows 97 38 268 137 145 32 64 128 256), losses := [] }

theorem u4919 : Upper (D 3) (R 3) [96,36,264,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4919
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4919
end Delivery.IrregularNine14.P03
