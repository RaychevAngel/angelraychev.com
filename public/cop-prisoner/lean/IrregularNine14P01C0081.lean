import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0024

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4860 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 275 98 52 140 17 234 202 202 458), lower := (rows 275 98 52 140 17 32 64 128 256), losses := [] }

theorem u4860 : Upper (D 1) (R 1) [274,96,48,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4860
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4861 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 52 140 18 233 201 201 457), lower := (rows 275 98 52 140 18 32 64 128 256), losses := [] }

theorem u4861 : Upper (D 1) (R 1) [274,96,48,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4861
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4862 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 275 98 52 140 24 227 195 195 451), lower := (rows 275 98 52 140 24 32 64 128 256), losses := [] }

theorem u4862 : Upper (D 1) (R 1) [274,96,48,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4862
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4863 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 52 140 80 171 203 139 395), lower := (rows 275 98 52 140 80 32 64 128 256), losses := [] }

theorem u4863 : Upper (D 1) (R 1) [274,96,48,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4863
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4864 : Route 9 := (fun mask => (mask,id))

def c4864 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4864 : Upper (D 1) (R 1) [274,96,48,132,128] 13 := by
  apply FastRouting.sound _ _ [274,96,48,132,128] 13 (by decide) (choices 1) [1,2,8,64] r4864 c4864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1457
  · exact u1458
  · exact u1459
  · exact u1460

def b4865 : PairBound 9 := { available := 142, camps := [], pairs := [], upper := (rows 275 98 52 200 17 174 206 142 398), lower := (rows 275 98 52 200 17 32 64 128 256), losses := [] }

theorem u4865 : Upper (D 1) (R 1) [274,96,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4865
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4866 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 52 200 18 173 205 141 397), lower := (rows 275 98 52 200 18 32 64 128 256), losses := [] }

theorem u4866 : Upper (D 1) (R 1) [274,96,48,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4866
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4867 : PairBound 9 := { available := 139, camps := [], pairs := [], upper := (rows 275 98 52 200 20 171 203 139 395), lower := (rows 275 98 52 200 20 32 64 128 256), losses := [] }

theorem u4867 : Upper (D 1) (R 1) [274,96,48,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4867
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4868 : PairBound 9 := { available := 135, camps := [], pairs := [], upper := (rows 275 98 52 200 24 167 199 135 391), lower := (rows 275 98 52 200 24 32 64 128 256), losses := [] }

theorem u4868 : Upper (D 1) (R 1) [274,96,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4868
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4869 : Route 9 := (fun mask => (mask,id))

def c4869 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4869 : Upper (D 1) (R 1) [274,96,48,192,128] 13 := by
  apply FastRouting.sound _ _ [274,96,48,192,128] 13 (by decide) (choices 1) [1,2,4,8] r4869 c4869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1461
  · exact u1462
  · exact u1463
  · exact u1464

def b4870 : PairBound 9 := { available := 120, camps := [], pairs := [], upper := (rows 275 98 133 138 20 120 120 248 376), lower := (rows 275 98 133 138 20 32 64 128 256), losses := [] }

theorem u4870 : Upper (D 1) (R 1) [274,96,129,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4870
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4871 : PairBound 9 := { available := 116, camps := [], pairs := [], upper := (rows 275 98 133 138 24 116 116 244 372), lower := (rows 275 98 133 138 24 32 64 128 256), losses := [] }

theorem u4871 : Upper (D 1) (R 1) [274,96,129,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4871
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4872 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 133 138 48 124 92 220 348), lower := (rows 275 98 133 138 48 32 64 128 256), losses := [] }

theorem u4872 : Upper (D 1) (R 1) [274,96,129,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4872
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4873 : PairBound 9 := { available := 108, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 133 152 18 108 108 236 364), lower := (rows 275 98 133 152 18 32 64 128 256), losses := [] }

theorem u4873 : Upper (D 1) (R 1) [274,96,129,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4873
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4874 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 275 98 133 152 20 106 106 234 362), lower := (rows 275 98 133 152 20 32 64 128 256), losses := [] }

theorem u4874 : Upper (D 1) (R 1) [274,96,129,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4874
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4875 : PairBound 9 := { available := 102, camps := [], pairs := [], upper := (rows 275 98 133 152 24 102 102 230 358), lower := (rows 275 98 133 152 24 32 64 128 256), losses := [] }

theorem u4875 : Upper (D 1) (R 1) [274,96,129,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4875
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4876 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 133 152 48 110 78 206 334), lower := (rows 275 98 133 152 48 32 64 128 256), losses := [] }

theorem u4876 : Upper (D 1) (R 1) [274,96,129,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4876
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4877 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 133 168 18 124 92 220 348), lower := (rows 275 98 133 168 18 32 64 128 256), losses := [] }

theorem u4877 : Upper (D 1) (R 1) [274,96,129,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4877
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4878 : PairBound 9 := { available := 90, camps := [], pairs := [], upper := (rows 275 98 133 168 20 122 90 218 346), lower := (rows 275 98 133 168 20 32 64 128 256), losses := [] }

theorem u4878 : Upper (D 1) (R 1) [274,96,129,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4878
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4879 : PairBound 9 := { available := 86, camps := [], pairs := [], upper := (rows 275 98 133 168 24 118 86 214 342), lower := (rows 275 98 133 168 24 32 64 128 256), losses := [] }

theorem u4879 : Upper (D 1) (R 1) [274,96,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4879
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4880 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 133 168 80 62 94 158 286), lower := (rows 275 98 133 168 80 32 64 128 256), losses := [] }

theorem u4880 : Upper (D 1) (R 1) [274,96,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4880
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4881 : PairBound 9 := { available := 108, camps := [], pairs := [], upper := (rows 275 98 134 152 17 108 108 236 364), lower := (rows 275 98 134 152 17 32 64 128 256), losses := [] }

theorem u4881 : Upper (D 1) (R 1) [274,96,130,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4881
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4882 : PairBound 9 := { available := 105, camps := [], pairs := [], upper := (rows 275 98 134 152 20 105 105 233 361), lower := (rows 275 98 134 152 20 32 64 128 256), losses := [] }

theorem u4882 : Upper (D 1) (R 1) [274,96,130,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4882
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4883 : PairBound 9 := { available := 101, camps := [], pairs := [], upper := (rows 275 98 134 152 24 101 101 229 357), lower := (rows 275 98 134 152 24 32 64 128 256), losses := [] }

theorem u4883 : Upper (D 1) (R 1) [274,96,130,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4883
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4884 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 134 152 48 109 77 205 333), lower := (rows 275 98 134 152 48 32 64 128 256), losses := [] }

theorem u4884 : Upper (D 1) (R 1) [274,96,130,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4884
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4885 : PairBound 9 := { available := 92, camps := [], pairs := [], upper := (rows 275 98 134 168 17 124 92 220 348), lower := (rows 275 98 134 168 17 32 64 128 256), losses := [] }

theorem u4885 : Upper (D 1) (R 1) [274,96,130,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4885
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4886 : PairBound 9 := { available := 89, camps := [], pairs := [], upper := (rows 275 98 134 168 20 121 89 217 345), lower := (rows 275 98 134 168 20 32 64 128 256), losses := [] }

theorem u4886 : Upper (D 1) (R 1) [274,96,130,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4886
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4887 : PairBound 9 := { available := 85, camps := [], pairs := [], upper := (rows 275 98 134 168 24 117 85 213 341), lower := (rows 275 98 134 168 24 32 64 128 256), losses := [] }

theorem u4887 : Upper (D 1) (R 1) [274,96,130,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4887
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4888 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 134 168 80 61 93 157 285), lower := (rows 275 98 134 168 80 32 64 128 256), losses := [] }

theorem u4888 : Upper (D 1) (R 1) [274,96,130,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4888
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4889 : PairBound 9 := { available := 78, camps := [], pairs := [], upper := (rows 275 98 148 168 17 110 78 206 334), lower := (rows 275 98 148 168 17 32 64 128 256), losses := [] }

theorem u4889 : Upper (D 1) (R 1) [274,96,144,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4889
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4890 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 148 168 18 109 77 205 333), lower := (rows 275 98 148 168 18 32 64 128 256), losses := [] }

theorem u4890 : Upper (D 1) (R 1) [274,96,144,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4890
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4891 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 275 98 148 168 20 107 75 203 331), lower := (rows 275 98 148 168 20 32 64 128 256), losses := [] }

theorem u4891 : Upper (D 1) (R 1) [274,96,144,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4891
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4892 : PairBound 9 := { available := 71, camps := [], pairs := [], upper := (rows 275 98 148 168 24 103 71 199 327), lower := (rows 275 98 148 168 24 32 64 128 256), losses := [] }

theorem u4892 : Upper (D 1) (R 1) [274,96,144,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4892
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4893 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 148 168 80 47 79 143 271), lower := (rows 275 98 148 168 80 32 64 128 256), losses := [] }

theorem u4893 : Upper (D 1) (R 1) [274,96,144,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4893
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4894 : PairBound 9 := { available := 30, camps := [], pairs := [], upper := (rows 275 98 164 200 17 62 94 158 286), lower := (rows 275 98 164 200 17 32 64 128 256), losses := [] }

theorem u4894 : Upper (D 1) (R 1) [274,96,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4894
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4895 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 164 200 18 61 93 157 285), lower := (rows 275 98 164 200 18 32 64 128 256), losses := [] }

theorem u4895 : Upper (D 1) (R 1) [274,96,160,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4895
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4896 : PairBound 9 := { available := 27, camps := [], pairs := [], upper := (rows 275 98 164 200 20 59 91 155 283), lower := (rows 275 98 164 200 20 32 64 128 256), losses := [] }

theorem u4896 : Upper (D 1) (R 1) [274,96,160,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4896
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4897 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 11 38 200 18 240 240 240 496), lower := (rows 277 11 38 200 18 32 64 128 256), losses := [] }

theorem u4897 : Upper (D 1) (R 1) [276,9,34,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4897
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4898 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 277 11 38 200 48 242 210 210 466), lower := (rows 277 11 38 200 48 32 64 128 256), losses := [] }

theorem u4898 : Upper (D 1) (R 1) [276,9,34,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4898
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4899 : Route 9 := (fun mask => (mask,id))

def c4899 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4899 : Upper (D 1) (R 1) [276,9,34,192,64] 13 := by
  apply FastRouting.sound _ _ [276,9,34,192,64] 13 (by decide) (choices 1) [2,16,128] r4899 c4899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1465
  · exact u1466
  · exact u1467

def b4900 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 277 11 100 42 18 240 208 208 464), lower := (rows 277 11 100 42 18 32 64 128 256), losses := [] }

theorem u4900 : Upper (D 1) (R 1) [276,9,96,34,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4900
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4901 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 11 100 42 80 178 210 146 402), lower := (rows 277 11 100 42 80 32 64 128 256), losses := [] }

theorem u4901 : Upper (D 1) (R 1) [276,9,96,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4901
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4902 : Route 9 := (fun mask => (mask,id))

def c4902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4902 : Upper (D 1) (R 1) [276,9,96,34,128] 13 := by
  apply FastRouting.sound _ _ [276,9,96,34,128] 13 (by decide) (choices 1) [2,16,64,128] r4902 c4902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1468
  · exact u1469
  · exact u1470
  · exact u1471

def b4903 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 277 11 100 138 18 240 240 240 496), lower := (rows 277 11 100 138 18 32 64 128 256), losses := [] }

theorem u4903 : Upper (D 1) (R 1) [276,9,96,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4903
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4904 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 277 11 100 138 48 242 210 210 466), lower := (rows 277 11 100 138 48 32 64 128 256), losses := [] }

theorem u4904 : Upper (D 1) (R 1) [276,9,96,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4904
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4905 : Route 9 := (fun mask => (mask,id))

def c4905 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4905 : Upper (D 1) (R 1) [276,9,96,130,128] 13 := by
  apply FastRouting.sound _ _ [276,9,96,130,128] 13 (by decide) (choices 1) [2,16,64] r4905 c4905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1472
  · exact u1473
  · exact u1474

def r4906 : Route 9 := (fun mask => (mask,id))

def c4906 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4906 : Upper (D 1) (R 1) [276,9,96,160,2] 13 := by
  apply FastRouting.sound _ _ [276,9,96,160,2] 13 (by decide) (choices 1) [2,16,64,128] r4906 c4906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1475
  · exact u1476
  · exact u1477
  · exact u1478

def b4907 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 11 100 168 80 178 210 146 402), lower := (rows 277 11 100 168 80 32 64 128 256), losses := [] }

theorem u4907 : Upper (D 1) (R 1) [276,9,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4907
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4908 : Route 9 := (fun mask => (mask,id))

def c4908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4908 : Upper (D 1) (R 1) [276,9,96,160,128] 13 := by
  apply FastRouting.sound _ _ [276,9,96,160,128] 13 (by decide) (choices 1) [2,16,64] r4908 c4908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1479
  · exact u1480
  · exact u1481

def b4909 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 277 26 38 200 17 226 226 226 482), lower := (rows 277 26 38 200 17 32 64 128 256), losses := [] }

theorem u4909 : Upper (D 1) (R 1) [276,24,34,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4909
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4910 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 277 26 38 200 18 225 225 225 481), lower := (rows 277 26 38 200 18 32 64 128 256), losses := [] }

theorem u4910 : Upper (D 1) (R 1) [276,24,34,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4910
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4911 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 277 26 38 200 48 227 195 195 451), lower := (rows 277 26 38 200 48 32 64 128 256), losses := [] }

theorem u4911 : Upper (D 1) (R 1) [276,24,34,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4911
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4912 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 277 26 38 200 80 163 227 163 419), lower := (rows 277 26 38 200 80 32 64 128 256), losses := [] }

theorem u4912 : Upper (D 1) (R 1) [276,24,34,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4912
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4913 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 26 100 42 17 226 194 194 450), lower := (rows 277 26 100 42 17 32 64 128 256), losses := [] }

theorem u4913 : Upper (D 1) (R 1) [276,24,96,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4913
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4914 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 26, targets := 64 }], pairs := [(1,6)], upper := (rows 277 26 100 42 18 225 193 193 449), lower := (rows 277 26 100 42 18 32 64 128 256), losses := [] }

theorem u4914 : Upper (D 1) (R 1) [276,24,96,34,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4914
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4915 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 26 100 42 80 163 195 131 387), lower := (rows 277 26 100 42 80 32 64 128 256), losses := [] }

theorem u4915 : Upper (D 1) (R 1) [276,24,96,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4915
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4916 : Route 9 := (fun mask => (mask,id))

def c4916 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4916 : Upper (D 1) (R 1) [276,24,96,34,128] 13 := by
  apply FastRouting.sound _ _ [276,24,96,34,128] 13 (by decide) (choices 1) [1,2,64,128] r4916 c4916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1482
  · exact u1483
  · exact u1484
  · exact u1485

def b4917 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 277 26 100 138 17 226 226 226 482), lower := (rows 277 26 100 138 17 32 64 128 256), losses := [] }

theorem u4917 : Upper (D 1) (R 1) [276,24,96,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4917
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4918 : PairBound 9 := { available := 225, camps := [{ cop := 7, region := 26, targets := 32 }], pairs := [(1,5)], upper := (rows 277 26 100 138 18 225 225 225 481), lower := (rows 277 26 100 138 18 32 64 128 256), losses := [] }

theorem u4918 : Upper (D 1) (R 1) [276,24,96,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4918
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4919 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 277 26 100 138 48 227 195 195 451), lower := (rows 277 26 100 138 48 32 64 128 256), losses := [] }

theorem u4919 : Upper (D 1) (R 1) [276,24,96,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4919
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4919
end Delivery.IrregularNine14.P01
