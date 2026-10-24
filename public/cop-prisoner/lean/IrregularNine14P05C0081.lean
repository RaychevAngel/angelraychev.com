import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0028
import IrregularNine14P05C0029

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4860 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 164 280 26 36 73 137 265), lower := (rows 35 70 164 280 26 36 64 128 256), losses := [] }

theorem u4860 : Upper (D 5) (R 5) [34,68,160,272,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4860
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4861 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 164 280 26 40 69 133 261), lower := (rows 35 70 164 280 26 40 64 128 256), losses := [] }

theorem u4861 : Upper (D 5) (R 5) [34,68,160,272,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4861
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4862 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 164 280 28 33 75 139 267), lower := (rows 35 70 164 280 28 33 64 128 256), losses := [] }

theorem u4862 : Upper (D 5) (R 5) [34,68,160,272,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4862
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4863 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 164 280 28 34 73 137 265), lower := (rows 35 70 164 280 28 34 64 128 256), losses := [] }

theorem u4863 : Upper (D 5) (R 5) [34,68,160,272,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4863
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4864 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 164 280 28 40 67 131 259), lower := (rows 35 70 164 280 28 40 64 128 256), losses := [] }

theorem u4864 : Upper (D 5) (R 5) [34,68,160,272,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4864
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4865 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 388 44 26 33 89 153 281), lower := (rows 35 70 388 44 26 33 64 128 256), losses := [] }

theorem u4865 : Upper (D 5) (R 5) [34,68,384,36,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4865
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4866 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 70 388 44 26 40 81 145 273), lower := (rows 35 70 388 44 26 40 64 128 256), losses := [] }

theorem u4866 : Upper (D 5) (R 5) [34,68,384,36,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4866
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4867 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 388 44 26 48 73 137 265), lower := (rows 35 70 388 44 26 48 64 128 256), losses := [] }

theorem u4867 : Upper (D 5) (R 5) [34,68,384,36,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4867
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4868 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 388 56 21 33 74 138 266), lower := (rows 35 70 388 56 21 33 64 128 256), losses := [] }

theorem u4868 : Upper (D 5) (R 5) [34,68,384,48,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4868
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4869 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 388 56 21 34 73 137 265), lower := (rows 35 70 388 56 21 34 64 128 256), losses := [] }

theorem u4869 : Upper (D 5) (R 5) [34,68,384,48,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4869
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4870 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 388 56 21 40 75 139 267), lower := (rows 35 70 388 56 21 40 64 128 256), losses := [] }

theorem u4870 : Upper (D 5) (R 5) [34,68,384,48,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4870
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4871 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 388 56 28 33 75 139 267), lower := (rows 35 70 388 56 28 33 64 128 256), losses := [] }

theorem u4871 : Upper (D 5) (R 5) [34,68,384,48,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4871
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4872 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 388 56 28 34 73 137 265), lower := (rows 35 70 388 56 28 34 64 128 256), losses := [] }

theorem u4872 : Upper (D 5) (R 5) [34,68,384,48,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4872
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4873 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 40 }], pairs := [(1,3),(1,5)], upper := (rows 35 70 388 56 28 40 67 131 259), lower := (rows 35 70 388 56 28 40 64 128 256), losses := [] }

theorem u4873 : Upper (D 5) (R 5) [34,68,384,48,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4873
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4874 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 396, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 82 44 392 25 33 70 134 262), lower := (rows 35 82 44 392 25 33 64 128 256), losses := [] }

theorem u4874 : Upper (D 5) (R 5) [34,80,40,384,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4874
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4875 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 44 392 25 34 69 133 261), lower := (rows 35 82 44 392 25 34 64 128 256), losses := [] }

theorem u4875 : Upper (D 5) (R 5) [34,80,40,384,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4875
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4876 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 82 44 392 25 36 71 135 263), lower := (rows 35 82 44 392 25 36 64 128 256), losses := [] }

theorem u4876 : Upper (D 5) (R 5) [34,80,40,384,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4876
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4877 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 133 265 28 34 108 172 300), lower := (rows 35 82 133 265 28 34 64 128 256), losses := [] }

theorem u4877 : Upper (D 5) (R 5) [34,80,129,257,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4877
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4878 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 264, targets := 4 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(3,2)], upper := (rows 35 82 133 265 28 36 106 170 298), lower := (rows 35 82 133 265 28 36 64 128 256), losses := [] }

theorem u4878 : Upper (D 5) (R 5) [34,80,129,257,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4878
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4879 : Route 9 := (fun mask => (mask,id))

def c4879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4879 : Upper (D 5) (R 5) [34,80,129,258,9,4] 13 := by
  apply FastRouting.sound _ _ [34,80,129,258,9,4] 13 (by decide) (choices 1) [4,8,32] r4879 c4879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1735
  · exact u1736
  · exact u1737

def b4880 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 132, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 82 133 266 25 40 100 164 292), lower := (rows 35 82 133 266 25 40 64 128 256), losses := [] }

theorem u4880 : Upper (D 5) (R 5) [34,80,129,258,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4880
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4881 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 82 133 266 28 33 108 172 300), lower := (rows 35 82 133 266 28 33 64 128 256), losses := [] }

theorem u4881 : Upper (D 5) (R 5) [34,80,129,258,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4881
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4882 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 264, targets := 4 }], pairs := [(0,3),(3,2)], upper := (rows 35 82 133 266 28 36 105 169 297), lower := (rows 35 82 133 266 28 36 64 128 256), losses := [{ target := 3, region := (rows 3 2 4 0 16 52 64 128 256), good := (rows 35 115 165 259 52 36 64 128 256) }] }

theorem u4882 : Upper (D 5) (R 5) [34,80,129,258,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4882
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4883 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 132, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 82 133 266 28 40 101 165 293), lower := (rows 35 82 133 266 28 40 64 128 256), losses := [] }

theorem u4883 : Upper (D 5) (R 5) [34,80,129,258,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4883
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4884 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 133 268 25 34 108 172 300), lower := (rows 35 82 133 268 25 34 64 128 256), losses := [] }

theorem u4884 : Upper (D 5) (R 5) [34,80,129,260,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4884
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4885 : Route 9 := (fun mask => (mask,id))

def c4885 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4885 : Upper (D 5) (R 5) [34,80,129,260,9,4] 13 := by
  apply FastRouting.sound _ _ [34,80,129,260,9,4] 13 (by decide) (choices 1) [2,8,32] r4885 c4885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1738
  · exact u1739
  · exact u1740

def b4886 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 132, targets := 8 }], pairs := [(0,2),(2,3)], upper := (rows 35 82 133 268 25 40 102 166 294), lower := (rows 35 82 133 268 25 40 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 56 64 128 256), good := (rows 35 115 129 296 57 40 64 128 256) }] }

theorem u4886 : Upper (D 5) (R 5) [34,80,129,260,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4886
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4887 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 82 133 296 28 33 78 142 270), lower := (rows 35 82 133 296 28 33 64 128 256), losses := [] }

theorem u4887 : Upper (D 5) (R 5) [34,80,129,288,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4887
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4888 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 133 296 28 34 77 141 269), lower := (rows 35 82 133 296 28 34 64 128 256), losses := [] }

theorem u4888 : Upper (D 5) (R 5) [34,80,129,288,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4888
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4889 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 264, targets := 4 }], pairs := [(0,3),(3,2)], upper := (rows 35 82 133 296 28 36 75 139 267), lower := (rows 35 82 133 296 28 36 64 128 256), losses := [{ target := 3, region := (rows 3 2 4 0 16 52 64 128 256), good := (rows 35 115 165 288 52 36 64 128 256) }] }

theorem u4889 : Upper (D 5) (R 5) [34,80,129,288,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4889
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4890 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 82 133 296 28 40 71 135 263), lower := (rows 35 82 133 296 28 40 64 128 256), losses := [] }

theorem u4890 : Upper (D 5) (R 5) [34,80,129,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4890
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4891 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 396, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 82 134 268 21 33 104 168 296), lower := (rows 35 82 134 268 21 33 64 128 256), losses := [] }

theorem u4891 : Upper (D 5) (R 5) [34,80,130,260,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4891
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4892 : Route 9 := (fun mask => (mask,id))

def c4892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4892 : Upper (D 5) (R 5) [34,80,130,260,5,8] 13 := by
  apply FastRouting.sound _ _ [34,80,130,260,5,8] 13 (by decide) (choices 1) [1,8,32] r4892 c4892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1741
  · exact u1742
  · exact u1743

def b4893 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 396, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 82 134 268 25 33 108 172 300), lower := (rows 35 82 134 268 25 33 64 128 256), losses := [] }

theorem u4893 : Upper (D 5) (R 5) [34,80,130,260,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4893
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4894 : Route 9 := (fun mask => (mask,id))

def c4894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4894 : Upper (D 5) (R 5) [34,80,130,260,9,4] 13 := by
  apply FastRouting.sound _ _ [34,80,130,260,9,4] 13 (by decide) (choices 1) [1,8,32] r4894 c4894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1744
  · exact u1745
  · exact u1746

def b4895 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 132, targets := 8 }], pairs := [(0,2),(2,3)], upper := (rows 35 82 134 268 25 40 101 165 293), lower := (rows 35 82 134 268 25 40 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 56 64 128 256), good := (rows 35 115 131 296 57 40 64 128 256) }] }

theorem u4895 : Upper (D 5) (R 5) [34,80,130,260,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4895
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4896 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 396, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 82 134 296 21 33 76 140 268), lower := (rows 35 82 134 296 21 33 64 128 256), losses := [] }

theorem u4896 : Upper (D 5) (R 5) [34,80,130,288,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4896
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4897 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 82 134 296 21 36 73 137 265), lower := (rows 35 82 134 296 21 36 64 128 256), losses := [] }

theorem u4897 : Upper (D 5) (R 5) [34,80,130,288,5,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4897
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4898 : PairBound 9 := { available := 13, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 82 134 296 21 40 77 141 269), lower := (rows 35 82 134 296 21 40 64 128 256), losses := [] }

theorem u4898 : Upper (D 5) (R 5) [34,80,130,288,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4898
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4899 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 82 134 296 28 33 77 141 269), lower := (rows 35 82 134 296 28 33 64 128 256), losses := [] }

theorem u4899 : Upper (D 5) (R 5) [34,80,130,288,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4899
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4900 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 82 134 296 28 36 73 137 265), lower := (rows 35 82 134 296 28 36 64 128 256), losses := [] }

theorem u4900 : Upper (D 5) (R 5) [34,80,130,288,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4900
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4901 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 82 134 296 28 40 69 133 261), lower := (rows 35 82 134 296 28 40 64 128 256), losses := [] }

theorem u4901 : Upper (D 5) (R 5) [34,80,130,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4901
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4902 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 396, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 82 140 268 21 33 106 170 298), lower := (rows 35 82 140 268 21 33 64 128 256), losses := [] }

theorem u4902 : Upper (D 5) (R 5) [34,80,136,260,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4902
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4903 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 140 268 21 34 105 169 297), lower := (rows 35 82 140 268 21 34 64 128 256), losses := [] }

theorem u4903 : Upper (D 5) (R 5) [34,80,136,260,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4903
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4904 : PairBound 9 := { available := 35, camps := [], pairs := [(0,2),(1,2)], upper := (rows 35 82 140 268 21 40 99 163 291), lower := (rows 35 82 140 268 21 40 64 128 256), losses := [{ target := 2, region := (rows 17 18 0 8 16 44 81 145 273), good := (rows 483 467 168 296 499 40 64 128 256) }] }

theorem u4904 : Upper (D 5) (R 5) [34,80,136,260,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4904
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4905 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 396, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 82 140 296 21 33 78 142 270), lower := (rows 35 82 140 296 21 33 64 128 256), losses := [] }

theorem u4905 : Upper (D 5) (R 5) [34,80,136,288,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4905
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4906 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 140 296 21 34 77 141 269), lower := (rows 35 82 140 296 21 34 64 128 256), losses := [] }

theorem u4906 : Upper (D 5) (R 5) [34,80,136,288,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4906
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4907 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 264, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 35 82 140 296 21 36 75 139 267), lower := (rows 35 82 140 296 21 36 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 9 16 32 81 145 273), good := (rows 491 466 136 296 475 32 64 128 256) }] }

theorem u4907 : Upper (D 5) (R 5) [34,80,136,288,5,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4907
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4908 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 82 140 296 21 40 71 135 263), lower := (rows 35 82 140 296 21 40 64 128 256), losses := [] }

theorem u4908 : Upper (D 5) (R 5) [34,80,136,288,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4908
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4909 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 194 52 265 26 33 76 140 268), lower := (rows 35 194 52 265 26 33 64 128 256), losses := [] }

theorem u4909 : Upper (D 5) (R 5) [34,192,48,257,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4909
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4910 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 194 52 265 26 36 77 141 269), lower := (rows 35 194 52 265 26 36 64 128 256), losses := [] }

theorem u4910 : Upper (D 5) (R 5) [34,192,48,257,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4910
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4911 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 195, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 194 52 265 26 40 69 133 261), lower := (rows 35 194 52 265 26 40 64 128 256), losses := [] }

theorem u4911 : Upper (D 5) (R 5) [34,192,48,257,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4911
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4912 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 194 52 265 28 33 78 142 270), lower := (rows 35 194 52 265 28 33 64 128 256), losses := [] }

theorem u4912 : Upper (D 5) (R 5) [34,192,48,257,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4912
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4913 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 52 265 28 34 77 141 269), lower := (rows 35 194 52 265 28 34 64 128 256), losses := [] }

theorem u4913 : Upper (D 5) (R 5) [34,192,48,257,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4913
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4914 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 194 52 265 28 36 75 139 267), lower := (rows 35 194 52 265 28 36 64 128 256), losses := [] }

theorem u4914 : Upper (D 5) (R 5) [34,192,48,257,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4914
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4915 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 194 52 265 28 40 71 135 263), lower := (rows 35 194 52 265 28 40 64 128 256), losses := [] }

theorem u4915 : Upper (D 5) (R 5) [34,192,48,257,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4915
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4916 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 458, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 194 52 266 25 33 76 140 268), lower := (rows 35 194 52 266 25 33 64 128 256), losses := [] }

theorem u4916 : Upper (D 5) (R 5) [34,192,48,258,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4916
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4917 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 35 194 52 266 25 36 77 141 269), lower := (rows 35 194 52 266 25 36 64 128 256), losses := [] }

theorem u4917 : Upper (D 5) (R 5) [34,192,48,258,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4917
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4918 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 195, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 194 52 266 25 40 69 133 261), lower := (rows 35 194 52 266 25 40 64 128 256), losses := [] }

theorem u4918 : Upper (D 5) (R 5) [34,192,48,258,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4918
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4919 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 194 52 266 28 33 77 141 269), lower := (rows 35 194 52 266 28 33 64 128 256), losses := [] }

theorem u4919 : Upper (D 5) (R 5) [34,192,48,258,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4919
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u4919
end Delivery.IrregularNine14.P05
