import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0029

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4920 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 194 52 266 28 36 73 137 265), lower := (rows 35 194 52 266 28 36 64 128 256), losses := [] }

theorem u4920 : Upper (D 5) (R 5) [34,192,48,258,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4920
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4921 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 194 52 266 28 40 69 133 261), lower := (rows 35 194 52 266 28 40 64 128 256), losses := [] }

theorem u4921 : Upper (D 5) (R 5) [34,192,48,258,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4921
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4922 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 458, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 194 52 268 25 33 78 142 270), lower := (rows 35 194 52 268 25 33 64 128 256), losses := [] }

theorem u4922 : Upper (D 5) (R 5) [34,192,48,260,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4922
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4923 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 52 268 25 34 77 141 269), lower := (rows 35 194 52 268 25 34 64 128 256), losses := [] }

theorem u4923 : Upper (D 5) (R 5) [34,192,48,260,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4923
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4924 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 194 52 268 25 36 75 139 267), lower := (rows 35 194 52 268 25 36 64 128 256), losses := [] }

theorem u4924 : Upper (D 5) (R 5) [34,192,48,260,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4924
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4925 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 195, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 194 52 268 25 40 71 135 263), lower := (rows 35 194 52 268 25 40 64 128 256), losses := [] }

theorem u4925 : Upper (D 5) (R 5) [34,192,48,260,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4925
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4926 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 194 52 268 26 33 77 141 269), lower := (rows 35 194 52 268 26 33 64 128 256), losses := [] }

theorem u4926 : Upper (D 5) (R 5) [34,192,48,260,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4926
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4927 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 194 52 268 26 36 73 137 265), lower := (rows 35 194 52 268 26 36 64 128 256), losses := [] }

theorem u4927 : Upper (D 5) (R 5) [34,192,48,260,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4927
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4928 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 195, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 194 52 268 26 40 69 133 261), lower := (rows 35 194 52 268 26 40 64 128 256), losses := [] }

theorem u4928 : Upper (D 5) (R 5) [34,192,48,260,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4928
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4929 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 330, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 49 67 133 266 22 36 104 168 296), lower := (rows 49 67 133 266 22 36 64 128 256), losses := [] }

theorem u4929 : Upper (D 5) (R 5) [48,65,129,258,6,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4929
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4930 : Route 9 := (fun mask => (mask,id))

def c4930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4930 : Upper (D 5) (R 5) [48,65,129,258,6,8] 13 := by
  apply FastRouting.sound _ _ [48,65,129,258,6,8] 13 (by decide) (choices 1) [4,8,32] r4930 c4930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1747
  · exact u1748
  · exact u1749

def b4931 : PairBound 9 := { available := 44, camps := [], pairs := [(0,2),(0,3)], upper := (rows 49 67 133 266 28 34 108 172 300), lower := (rows 49 67 133 266 28 34 64 128 256), losses := [{ target := 2, region := (rows 17 2 0 8 16 42 64 128 256), good := (rows 49 99 129 298 57 34 64 128 256) },{ target := 3, region := (rows 17 2 4 0 16 42 64 128 256), good := (rows 49 99 133 290 53 34 64 128 256) }] }

theorem u4931 : Upper (D 5) (R 5) [48,65,129,258,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4931
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4932 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 330, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 49 67 133 266 28 36 106 170 298), lower := (rows 49 67 133 266 28 36 64 128 256), losses := [] }

theorem u4932 : Upper (D 5) (R 5) [48,65,129,258,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4932
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4933 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 198, targets := 8 }], pairs := [(1,3),(2,3)], upper := (rows 49 67 133 266 28 40 102 166 294), lower := (rows 49 67 133 266 28 40 64 128 256), losses := [] }

theorem u4933 : Upper (D 5) (R 5) [48,65,129,258,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4933
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4934 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 49 67 133 296 22 34 76 140 268), lower := (rows 49 67 133 296 22 34 64 128 256), losses := [] }

theorem u4934 : Upper (D 5) (R 5) [48,65,129,288,6,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4934
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4935 : PairBound 9 := { available := 14, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 49 67 133 296 22 40 78 142 270), lower := (rows 49 67 133 296 22 40 64 128 256), losses := [] }

theorem u4935 : Upper (D 5) (R 5) [48,65,129,288,6,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4935
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4936 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 49 67 133 296 26 34 76 140 268), lower := (rows 49 67 133 296 26 34 64 128 256), losses := [] }

theorem u4936 : Upper (D 5) (R 5) [48,65,129,288,10,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4936
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4937 : Route 9 := (fun mask => (mask,id))

def c4937 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4937 : Upper (D 5) (R 5) [48,65,129,288,10,4] 13 := by
  apply FastRouting.sound _ _ [48,65,129,288,10,4] 13 (by decide) (choices 1) [2,4,8] r4937 c4937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1750
  · exact u1751
  · exact u1752

def b4938 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 198, targets := 40 }], pairs := [(1,3),(1,5)], upper := (rows 49 67 133 296 26 40 70 134 262), lower := (rows 49 67 133 296 26 40 64 128 256), losses := [] }

theorem u4938 : Upper (D 5) (R 5) [48,65,129,288,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4938
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4939 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 49 67 134 266 28 33 108 172 300), lower := (rows 49 67 134 266 28 33 64 128 256), losses := [] }

theorem u4939 : Upper (D 5) (R 5) [48,65,130,258,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4939
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4940 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 330, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 49 67 134 266 28 36 105 169 297), lower := (rows 49 67 134 266 28 36 64 128 256), losses := [] }

theorem u4940 : Upper (D 5) (R 5) [48,65,130,258,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4940
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4941 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 67 134 268 26 33 108 172 300), lower := (rows 49 67 134 268 26 33 64 128 256), losses := [] }

theorem u4941 : Upper (D 5) (R 5) [48,65,130,260,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4941
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4942 : PairBound 9 := { available := 41, camps := [], pairs := [(0,1),(0,3)], upper := (rows 49 67 134 268 26 36 105 169 297), lower := (rows 49 67 134 268 26 36 64 128 256), losses := [{ target := 1, region := (rows 17 0 4 8 16 44 80 144 272), good := (rows 497 65 164 300 505 36 64 128 256) },{ target := 3, region := (rows 17 2 4 0 16 44 64 128 256), good := (rows 49 67 166 292 51 36 64 128 256) }] }

theorem u4942 : Upper (D 5) (R 5) [48,65,130,260,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4942
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4943 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 198, targets := 8 }], pairs := [(1,3),(2,3)], upper := (rows 49 67 134 268 26 40 101 165 293), lower := (rows 49 67 134 268 26 40 64 128 256), losses := [] }

theorem u4943 : Upper (D 5) (R 5) [48,65,130,260,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4943
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4944 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 67 134 296 26 33 76 140 268), lower := (rows 49 67 134 296 26 33 64 128 256), losses := [] }

theorem u4944 : Upper (D 5) (R 5) [48,65,130,288,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4944
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4945 : Route 9 := (fun mask => (mask,id))

def c4945 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4945 : Upper (D 5) (R 5) [48,65,130,288,10,4] 13 := by
  apply FastRouting.sound _ _ [48,65,130,288,10,4] 13 (by decide) (choices 1) [1,4,8] r4945 c4945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1753
  · exact u1754
  · exact u1755

def b4946 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 198, targets := 40 }], pairs := [(1,3),(1,5)], upper := (rows 49 67 134 296 26 40 69 133 261), lower := (rows 49 67 134 296 26 40 64 128 256), losses := [] }

theorem u4946 : Upper (D 5) (R 5) [48,65,130,288,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4946
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4947 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 67 134 296 28 33 78 142 270), lower := (rows 49 67 134 296 28 33 64 128 256), losses := [] }

theorem u4947 : Upper (D 5) (R 5) [48,65,130,288,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4947
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4948 : PairBound 9 := { available := 13, camps := [], pairs := [(0,2),(0,3)], upper := (rows 49 67 134 296 28 34 77 141 269), lower := (rows 49 67 134 296 28 34 64 128 256), losses := [{ target := 2, region := (rows 17 2 0 8 16 38 64 128 256), good := (rows 49 99 162 296 57 34 64 128 256) },{ target := 3, region := (rows 17 2 4 0 16 38 64 128 256), good := (rows 49 99 166 288 53 34 64 128 256) }] }

theorem u4948 : Upper (D 5) (R 5) [48,65,130,288,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4948
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4949 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 330, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 49 67 134 296 28 36 75 139 267), lower := (rows 49 67 134 296 28 36 64 128 256), losses := [] }

theorem u4949 : Upper (D 5) (R 5) [48,65,130,288,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4949
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4950 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 198, targets := 40 }], pairs := [(1,3),(1,5)], upper := (rows 49 67 134 296 28 40 71 135 263), lower := (rows 49 67 134 296 28 40 64 128 256), losses := [] }

theorem u4950 : Upper (D 5) (R 5) [48,65,130,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4950
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4951 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 67 140 268 22 33 106 170 298), lower := (rows 49 67 140 268 22 33 64 128 256), losses := [] }

theorem u4951 : Upper (D 5) (R 5) [48,65,136,260,6,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4951
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4952 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 49 67 140 268 22 34 105 169 297), lower := (rows 49 67 140 268 22 34 64 128 256), losses := [] }

theorem u4952 : Upper (D 5) (R 5) [48,65,136,260,6,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4952
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4953 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 66, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 49 67 140 268 22 40 99 163 291), lower := (rows 49 67 140 268 22 40 64 128 256), losses := [] }

theorem u4953 : Upper (D 5) (R 5) [48,65,136,260,6,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4953
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4954 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 67 140 296 22 33 78 142 270), lower := (rows 49 67 140 296 22 33 64 128 256), losses := [] }

theorem u4954 : Upper (D 5) (R 5) [48,65,136,288,6,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4954
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4955 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 49 67 140 296 22 34 77 141 269), lower := (rows 49 67 140 296 22 34 64 128 256), losses := [] }

theorem u4955 : Upper (D 5) (R 5) [48,65,136,288,6,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4955
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4956 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 330, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 49 67 140 296 22 36 75 139 267), lower := (rows 49 67 140 296 22 36 64 128 256), losses := [] }

theorem u4956 : Upper (D 5) (R 5) [48,65,136,288,6,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4956
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4957 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 49 67 140 296 22 40 71 135 263), lower := (rows 49 67 140 296 22 40 64 128 256), losses := [] }

theorem u4957 : Upper (D 5) (R 5) [48,65,136,288,6,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4957
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4958 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 67 140 296 26 33 70 134 262), lower := (rows 49 67 140 296 26 33 64 128 256), losses := [] }

theorem u4958 : Upper (D 5) (R 5) [48,65,136,288,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4958
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4959 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 49 67 140 296 26 34 69 133 261), lower := (rows 49 67 140 296 26 34 64 128 256), losses := [] }

theorem u4959 : Upper (D 5) (R 5) [48,65,136,288,10,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4959
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4960 : Route 9 := (fun mask => (mask,id))

def c4960 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4960 : Upper (D 5) (R 5) [48,65,136,288,10,4] 13 := by
  apply FastRouting.sound _ _ [48,65,136,288,10,4] 13 (by decide) (choices 1) [1,2,4] r4960 c4960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1756
  · exact u1757
  · exact u1758

def b4961 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 49, targets := 10 }], pairs := [(0,1),(0,3)], upper := (rows 49 70 134 266 21 33 104 168 296), lower := (rows 49 70 134 266 21 33 64 128 256), losses := [] }

theorem u4961 : Upper (D 5) (R 5) [48,68,130,258,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4961
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4962 : Route 9 := (fun mask => (mask,id))

def c4962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4962 : Upper (D 5) (R 5) [48,68,130,258,5,8] 13 := by
  apply FastRouting.sound _ _ [48,68,130,258,5,8] 13 (by decide) (choices 1) [1,8,32] r4962 c4962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1759
  · exact u1760
  · exact u1761

def b4963 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 70 134 266 25 33 108 172 300), lower := (rows 49 70 134 266 25 33 64 128 256), losses := [] }

theorem u4963 : Upper (D 5) (R 5) [48,68,130,258,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4963
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4964 : PairBound 9 := { available := 41, camps := [], pairs := [(0,1),(4,1)], upper := (rows 49 70 134 266 25 36 105 169 297), lower := (rows 49 70 134 266 25 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 24 38 72 136 264), good := (rows 49 100 164 505 473 36 64 128 256) }] }

theorem u4964 : Upper (D 5) (R 5) [48,68,130,258,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4964
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4965 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 70 134 266 25 40 101 165 293), lower := (rows 49 70 134 266 25 40 64 128 256), losses := [] }

theorem u4965 : Upper (D 5) (R 5) [48,68,130,258,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4965
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4966 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 49 70 134 296 19 33 76 140 268), lower := (rows 49 70 134 296 19 33 64 128 256), losses := [] }

theorem u4966 : Upper (D 5) (R 5) [48,68,130,288,3,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4966
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4967 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 49 70 134 296 19 36 73 137 265), lower := (rows 49 70 134 296 19 36 64 128 256), losses := [] }

theorem u4967 : Upper (D 5) (R 5) [48,68,130,288,3,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4967
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4968 : PairBound 9 := { available := 13, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 49 70 134 296 19 40 77 141 269), lower := (rows 49 70 134 296 19 40 64 128 256), losses := [] }

theorem u4968 : Upper (D 5) (R 5) [48,68,130,288,3,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4968
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4969 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 70 134 296 26 33 77 141 269), lower := (rows 49 70 134 296 26 33 64 128 256), losses := [] }

theorem u4969 : Upper (D 5) (R 5) [48,68,130,288,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4969
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4970 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 49 70 134 296 26 36 73 137 265), lower := (rows 49 70 134 296 26 36 64 128 256), losses := [] }

theorem u4970 : Upper (D 5) (R 5) [48,68,130,288,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4970
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4971 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 198, targets := 40 }], pairs := [(1,3),(1,5)], upper := (rows 49 70 134 296 26 40 69 133 261), lower := (rows 49 70 134 296 26 40 64 128 256), losses := [] }

theorem u4971 : Upper (D 5) (R 5) [48,68,130,288,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4971
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4972 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 49 70 140 266 19 33 108 172 300), lower := (rows 49 70 140 266 19 33 64 128 256), losses := [] }

theorem u4972 : Upper (D 5) (R 5) [48,68,136,258,3,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4972
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4973 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 49 70 140 266 19 36 105 169 297), lower := (rows 49 70 140 266 19 36 64 128 256), losses := [] }

theorem u4973 : Upper (D 5) (R 5) [48,68,136,258,3,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4973
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4974 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 49 70 140 266 19 40 101 165 293), lower := (rows 49 70 140 266 19 40 64 128 256), losses := [] }

theorem u4974 : Upper (D 5) (R 5) [48,68,136,258,3,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4974
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4975 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 49 70 140 296 19 33 78 142 270), lower := (rows 49 70 140 296 19 33 64 128 256), losses := [] }

theorem u4975 : Upper (D 5) (R 5) [48,68,136,288,3,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4975
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4976 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 49 70 140 296 19 34 77 141 269), lower := (rows 49 70 140 296 19 34 64 128 256), losses := [] }

theorem u4976 : Upper (D 5) (R 5) [48,68,136,288,3,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4976
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4977 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 49 70 140 296 19 36 75 139 267), lower := (rows 49 70 140 296 19 36 64 128 256), losses := [] }

theorem u4977 : Upper (D 5) (R 5) [48,68,136,288,3,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4977
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4978 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 49 70 140 296 19 40 71 135 263), lower := (rows 49 70 140 296 19 40 64 128 256), losses := [] }

theorem u4978 : Upper (D 5) (R 5) [48,68,136,288,3,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4978
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4979 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 49, targets := 10 }], pairs := [(0,1),(0,3)], upper := (rows 49 70 140 296 21 33 74 138 266), lower := (rows 49 70 140 296 21 33 64 128 256), losses := [] }

theorem u4979 : Upper (D 5) (R 5) [48,68,136,288,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4979
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u4979
end Delivery.IrregularNine14.P05
