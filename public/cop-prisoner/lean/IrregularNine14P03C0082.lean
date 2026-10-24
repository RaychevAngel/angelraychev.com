import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0030
import IrregularNine14P03C0031

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4920 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 137 146 113 81 209 337), lower := (rows 97 38 268 137 146 32 64 128 256), losses := [] }

theorem u4920 : Upper (D 3) (R 3) [96,36,264,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4920
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4921 : Route 9 := (fun mask => (mask,id))

def c4921 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4921 : Upper (D 3) (R 3) [96,36,264,129,192] 13 := by
  apply FastRouting.sound _ _ [96,36,264,129,192] 13 (by decide) (choices 1) [1,2,16] r4921 c4921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1842
  · exact u1843
  · exact u1844

def b4922 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 268 138 145 113 81 209 337), lower := (rows 97 38 268 138 145 32 64 128 256), losses := [] }

theorem u4922 : Upper (D 3) (R 3) [96,36,264,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4922
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4923 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 268 138 208 49 81 145 273), lower := (rows 97 38 268 138 208 32 64 128 256), losses := [] }

theorem u4923 : Upper (D 3) (R 3) [96,36,264,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4923
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4924 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 152 145 99 67 195 323), lower := (rows 97 38 268 152 145 32 64 128 256), losses := [] }

theorem u4924 : Upper (D 3) (R 3) [96,36,264,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4924
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4925 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 152 146 97 65 193 321), lower := (rows 97 38 268 152 146 32 64 128 256), losses := [] }

theorem u4925 : Upper (D 3) (R 3) [96,36,264,144,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4925
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4926 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 152 208 35 67 131 259), lower := (rows 97 38 268 152 208 32 64 128 256), losses := [] }

theorem u4926 : Upper (D 3) (R 3) [96,36,264,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4926
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4927 : Route 9 := (fun mask => (mask,id))

def c4927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4927 : Upper (D 3) (R 3) [96,36,264,192,129] 13 := by
  apply FastRouting.sound _ _ [96,36,264,192,129] 13 (by decide) (choices 1) [1,2,16] r4927 c4927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1845
  · exact u1846
  · exact u1847

def b4928 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 200 146 49 81 145 273), lower := (rows 97 38 268 200 146 32 64 128 256), losses := [] }

theorem u4928 : Upper (D 3) (R 3) [96,36,264,192,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4928
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4929 : PairBound 9 := { available := 27, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 324 137 145 59 91 155 283), lower := (rows 97 38 324 137 145 32 64 128 256), losses := [] }

theorem u4929 : Upper (D 3) (R 3) [96,36,320,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4929
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4930 : Route 9 := (fun mask => (mask,id))

def c4930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4930 : Upper (D 3) (R 3) [96,36,320,129,130] 13 := by
  apply FastRouting.sound _ _ [96,36,320,129,130] 13 (by decide) (choices 1) [1,8,16] r4930 c4930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1848
  · exact u1849
  · exact u1850

def b4931 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 324 137 152 51 83 147 275), lower := (rows 97 38 324 137 152 32 64 128 256), losses := [] }

theorem u4931 : Upper (D 3) (R 3) [96,36,320,129,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4931
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4932 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 324 138 152 49 81 145 273), lower := (rows 97 38 324 138 152 32 64 128 256), losses := [] }

theorem u4932 : Upper (D 3) (R 3) [96,36,320,130,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4932
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4933 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 324 152 152 35 67 131 259), lower := (rows 97 38 324 152 152 32 64 128 256), losses := [] }

theorem u4933 : Upper (D 3) (R 3) [96,36,320,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4933
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4934 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 138 273 61 93 157 285), lower := (rows 97 98 133 138 273 32 64 128 256), losses := [] }

theorem u4934 : Upper (D 3) (R 3) [96,96,129,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4934
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4935 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 138 276 57 89 153 281), lower := (rows 97 98 133 138 276 32 64 128 256), losses := [] }

theorem u4935 : Upper (D 3) (R 3) [96,96,129,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4935
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4936 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 138 280 53 85 149 277), lower := (rows 97 98 133 138 280 32 64 128 256), losses := [] }

theorem u4936 : Upper (D 3) (R 3) [96,96,129,130,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4936
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4937 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 152 273 47 79 143 271), lower := (rows 97 98 133 152 273 32 64 128 256), losses := [] }

theorem u4937 : Upper (D 3) (R 3) [96,96,129,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4937
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4938 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 152 274 45 77 141 269), lower := (rows 97 98 133 152 274 32 64 128 256), losses := [] }

theorem u4938 : Upper (D 3) (R 3) [96,96,129,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4938
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4939 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 134 152 273 45 77 141 269), lower := (rows 97 98 134 152 273 32 64 128 256), losses := [] }

theorem u4939 : Upper (D 3) (R 3) [96,96,130,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4939
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4940 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 22, targets := 64 }], pairs := [(1,6)], upper := (rows 259 7 28 41 49 224 192 192 448), lower := (rows 259 7 28 41 49 32 64 128 256), losses := [] }

theorem u4940 : Upper (D 3) (R 3) [258,5,24,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4940
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4941 : Route 9 := (fun mask => (mask,id))

def c4941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4941 : Upper (D 3) (R 3) [258,5,24,33,65] 13 := by
  apply FastRouting.sound _ _ [258,5,24,33,65] 13 (by decide) (choices 1) [64,128] r4941 c4941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1851
  · exact u1852

def b4942 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 451, targets := 32 }], pairs := [(0,5)], upper := (rows 259 7 28 41 112 225 193 193 449), lower := (rows 259 7 28 41 112 32 64 128 256), losses := [] }

theorem u4942 : Upper (D 3) (R 3) [258,5,24,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4942
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4943 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c4943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4943 : Upper (D 3) (R 3) [258,5,24,33,192] 13 := by
  apply FastRouting.sound _ _ [258,5,24,33,192] 13 (by decide) (choices 1) [1,64] r4943 c4943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1853
  · exact u1854

def b4944 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 28 104 112 161 193 129 385), lower := (rows 259 7 28 104 112 32 64 128 256), losses := [] }

theorem u4944 : Upper (D 3) (R 3) [258,5,24,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4944
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4945 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 451, targets := 32 }], pairs := [(0,5)], upper := (rows 259 7 28 104 176 225 193 193 449), lower := (rows 259 7 28 104 176 32 64 128 256), losses := [] }

theorem u4945 : Upper (D 3) (R 3) [258,5,24,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4945
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4946 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 259 7 44 25 49 224 192 192 448), lower := (rows 259 7 44 25 49 32 64 128 256), losses := [] }

theorem u4946 : Upper (D 3) (R 3) [258,5,40,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4946
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4947 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 7 44 25 81 224 224 224 480), lower := (rows 259 7 44 25 81 32 64 128 256), losses := [] }

theorem u4947 : Upper (D 3) (R 3) [258,5,40,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4947
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4948 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 451, targets := 32 }], pairs := [(0,5)], upper := (rows 259 7 44 25 112 225 193 193 449), lower := (rows 259 7 44 25 112 32 64 128 256), losses := [] }

theorem u4948 : Upper (D 3) (R 3) [258,5,40,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4948
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4949 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c4949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4949 : Upper (D 3) (R 3) [258,5,40,17,192] 13 := by
  apply FastRouting.sound _ _ [258,5,40,17,192] 13 (by decide) (choices 1) [1,64] r4949 c4949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1855
  · exact u1856

def b4950 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 259 7 44 73 49 240 208 208 464), lower := (rows 259 7 44 73 49 32 64 128 256), losses := [] }

theorem u4950 : Upper (D 3) (R 3) [258,5,40,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4950
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4951 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 7 44 73 81 176 240 176 432), lower := (rows 259 7 44 73 81 32 64 128 256), losses := [] }

theorem u4951 : Upper (D 3) (R 3) [258,5,40,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4951
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4952 : Route 9 := (fun mask => (mask,id))

def c4952 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4952 : Upper (D 3) (R 3) [258,5,40,65,96] 13 := by
  apply FastRouting.sound _ _ [258,5,40,65,96] 13 (by decide) (choices 1) [1,16,128] r4952 c4952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1857
  · exact u1858
  · exact u1859

def r4953 : Route 9 := (fun mask => (mask,id))

def c4953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4953 : Upper (D 3) (R 3) [258,5,40,65,129] 13 := by
  apply FastRouting.sound _ _ [258,5,40,65,129] 13 (by decide) (choices 1) [16,64,128] r4953 c4953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1860
  · exact u1861
  · exact u1862

def r4954 : Route 9 := (fun mask => (mask,id))

def c4954 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4954 : Upper (D 3) (R 3) [258,5,40,65,160] 13 := by
  apply FastRouting.sound _ _ [258,5,40,65,160] 13 (by decide) (choices 1) [1,16,64,128] r4954 c4954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1863
  · exact u1864
  · exact u1865
  · exact u1866

def r4955 : Route 9 := (fun mask => (mask,id))

def c4955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4955 : Upper (D 3) (R 3) [258,5,40,65,192] 13 := by
  apply FastRouting.sound _ _ [258,5,40,65,192] 13 (by decide) (choices 1) [1,16,128] r4955 c4955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1867
  · exact u1868
  · exact u1869

def b4956 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 451, targets := 32 }], pairs := [(0,5)], upper := (rows 259 7 44 88 49 225 193 193 449), lower := (rows 259 7 44 88 49 32 64 128 256), losses := [] }

theorem u4956 : Upper (D 3) (R 3) [258,5,40,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4956
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4957 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 44 88 81 161 225 161 417), lower := (rows 259 7 44 88 81 32 64 128 256), losses := [] }

theorem u4957 : Upper (D 3) (R 3) [258,5,40,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4957
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4958 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 44 88 112 161 193 129 385), lower := (rows 259 7 44 88 112 32 64 128 256), losses := [] }

theorem u4958 : Upper (D 3) (R 3) [258,5,40,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4958
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4959 : Route 9 := (fun mask => (mask,id))

def c4959 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4959 : Upper (D 3) (R 3) [258,5,40,80,129] 13 := by
  apply FastRouting.sound _ _ [258,5,40,80,129] 13 (by decide) (choices 1) [1,64,128] r4959 c4959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1870
  · exact u1871
  · exact u1872

def b4960 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 451, targets := 32 }], pairs := [(0,5)], upper := (rows 259 7 44 88 176 225 193 193 449), lower := (rows 259 7 44 88 176 32 64 128 256), losses := [] }

theorem u4960 : Upper (D 3) (R 3) [258,5,40,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4960
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4961 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 44 88 208 161 225 161 417), lower := (rows 259 7 44 88 208 32 64 128 256), losses := [] }

theorem u4961 : Upper (D 3) (R 3) [258,5,40,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4961
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4962 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 259 7 44 200 49 241 209 209 465), lower := (rows 259 7 44 200 49 32 64 128 256), losses := [] }

theorem u4962 : Upper (D 3) (R 3) [258,5,40,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4962
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4963 : Route 9 := (fun mask => (mask,id))

def c4963 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4963 : Upper (D 3) (R 3) [258,5,40,192,65] 13 := by
  apply FastRouting.sound _ _ [258,5,40,192,65] 13 (by decide) (choices 1) [1,16,128] r4963 c4963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1873
  · exact u1874
  · exact u1875

def r4964 : Route 9 := (fun mask => (mask,id))

def c4964 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4964 : Upper (D 3) (R 3) [258,5,40,192,96] 13 := by
  apply FastRouting.sound _ _ [258,5,40,192,96] 13 (by decide) (choices 1) [1,16,128] r4964 c4964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1876
  · exact u1877
  · exact u1878

def b4965 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 7 44 200 208 49 113 177 305), lower := (rows 259 7 44 200 208 32 64 128 256), losses := [] }

theorem u4965 : Upper (D 3) (R 3) [258,5,40,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4965
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4966 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 259 7 100 25 25 224 224 224 480), lower := (rows 259 7 100 25 25 32 64 128 256), losses := [] }

theorem u4966 : Upper (D 3) (R 3) [258,5,96,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4966
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4967 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 7 100 25 49 232 200 200 456), lower := (rows 259 7 100 25 49 32 64 128 256), losses := [] }

theorem u4967 : Upper (D 3) (R 3) [258,5,96,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4967
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4968 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 387, targets := 32 }], pairs := [(0,5)], upper := (rows 259 7 100 25 56 225 193 193 449), lower := (rows 259 7 100 25 56 32 64 128 256), losses := [] }

theorem u4968 : Upper (D 3) (R 3) [258,5,96,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4968
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4969 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 7 100 25 112 169 201 137 393), lower := (rows 259 7 100 25 112 32 64 128 256), losses := [] }

theorem u4969 : Upper (D 3) (R 3) [258,5,96,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4969
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4970 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 7 100 25 145 232 232 232 488), lower := (rows 259 7 100 25 145 32 64 128 256), losses := [] }

theorem u4970 : Upper (D 3) (R 3) [258,5,96,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4970
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4971 : Route 9 := (fun mask => (mask,id))

def c4971 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4971 : Upper (D 3) (R 3) [258,5,96,17,136] 13 := by
  apply FastRouting.sound _ _ [258,5,96,17,136] 13 (by decide) (choices 1) [1,64,128] r4971 c4971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1879
  · exact u1880
  · exact u1881

def r4972 : Route 9 := (fun mask => (mask,id))

def c4972 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4972 : Upper (D 3) (R 3) [258,5,96,17,160] 13 := by
  apply FastRouting.sound _ _ [258,5,96,17,160] 13 (by decide) (choices 1) [1,8,64,128] r4972 c4972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1882
  · exact u1883
  · exact u1884
  · exact u1885

def b4973 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 7 100 41 88 177 209 145 401), lower := (rows 259 7 100 41 88 32 64 128 256), losses := [] }

theorem u4973 : Upper (D 3) (R 3) [258,5,96,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4973
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4974 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 7 100 41 145 248 216 216 472), lower := (rows 259 7 100 41 145 32 64 128 256), losses := [] }

theorem u4974 : Upper (D 3) (R 3) [258,5,96,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4974
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4975 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 7 100 41 152 241 209 209 465), lower := (rows 259 7 100 41 152 32 64 128 256), losses := [] }

theorem u4975 : Upper (D 3) (R 3) [258,5,96,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4975
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4976 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 7 100 41 208 185 217 153 409), lower := (rows 259 7 100 41 208 32 64 128 256), losses := [] }

theorem u4976 : Upper (D 3) (R 3) [258,5,96,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4976
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4977 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 100 56 88 161 193 129 385), lower := (rows 259 7 100 56 88 32 64 128 256), losses := [] }

theorem u4977 : Upper (D 3) (R 3) [258,5,96,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4977
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4978 : Route 9 := (fun mask => (mask,id))

def c4978 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4978 : Upper (D 3) (R 3) [258,5,96,48,129] 13 := by
  apply FastRouting.sound _ _ [258,5,96,48,129] 13 (by decide) (choices 1) [1,8,64,128] r4978 c4978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1886
  · exact u1887
  · exact u1888
  · exact u1889

def b4979 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 387, targets := 32 }], pairs := [(0,5)], upper := (rows 259 7 100 56 152 225 193 193 449), lower := (rows 259 7 100 56 152 32 64 128 256), losses := [] }

theorem u4979 : Upper (D 3) (R 3) [258,5,96,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4979
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4979
end Delivery.IrregularNine14.P03
