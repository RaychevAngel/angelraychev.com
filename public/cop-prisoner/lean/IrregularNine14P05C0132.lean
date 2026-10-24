import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0071

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7920 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 19 194 37 266 21 44 108 172 300), lower := (rows 19 194 37 266 21 32 64 128 256), losses := [] }

theorem u7920 : Upper (D 5) (R 5) [18,192,33,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7920
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7921 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 194 37 266 25 44 108 172 300), lower := (rows 19 194 37 266 25 32 64 128 256), losses := [] }

theorem u7921 : Upper (D 5) (R 5) [18,192,33,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7921
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7922 : Route 9 := (fun mask => (mask,id))

def c7922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7922 : Upper (D 5) (R 5) [18,192,33,258,12] 13 := by
  apply FastRouting.sound _ _ [18,192,33,258,12] 13 (by decide) (choices 1) [1,4,8] r7922 c7922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4276
  · exact u4277
  · exact u4278

def b7923 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 194 37 266 49 44 76 140 268), lower := (rows 19 194 37 266 49 32 64 128 256), losses := [] }

theorem u7923 : Upper (D 5) (R 5) [18,192,33,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7923
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7924 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 37 266 52 45 77 141 269), lower := (rows 19 194 37 266 52 32 64 128 256), losses := [] }

theorem u7924 : Upper (D 5) (R 5) [18,192,33,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7924
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7925 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 194 37 266 56 45 77 141 269), lower := (rows 19 194 37 266 56 32 64 128 256), losses := [] }

theorem u7925 : Upper (D 5) (R 5) [18,192,33,258,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7925
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7926 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 37 268 19 44 108 172 300), lower := (rows 19 194 37 268 19 32 64 128 256), losses := [] }

theorem u7926 : Upper (D 5) (R 5) [18,192,33,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7926
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7927 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 19 194 37 268 21 42 106 170 298), lower := (rows 19 194 37 268 21 32 64 128 256), losses := [] }

theorem u7927 : Upper (D 5) (R 5) [18,192,33,260,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7927
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7928 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 37 268 22 41 105 169 297), lower := (rows 19 194 37 268 22 32 64 128 256), losses := [] }

theorem u7928 : Upper (D 5) (R 5) [18,192,33,260,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7928
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7929 : PairBound 9 := { available := 46, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 194 37 268 25 46 110 174 302), lower := (rows 19 194 37 268 25 32 64 128 256), losses := [] }

theorem u7929 : Upper (D 5) (R 5) [18,192,33,260,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7929
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7930 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 37 268 26 45 109 173 301), lower := (rows 19 194 37 268 26 32 64 128 256), losses := [] }

theorem u7930 : Upper (D 5) (R 5) [18,192,33,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7930
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7931 : PairBound 9 := { available := 43, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 37 268 28 43 107 171 299), lower := (rows 19 194 37 268 28 32 64 128 256), losses := [] }

theorem u7931 : Upper (D 5) (R 5) [18,192,33,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7931
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7932 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 194 37 268 49 46 78 142 270), lower := (rows 19 194 37 268 49 32 64 128 256), losses := [] }

theorem u7932 : Upper (D 5) (R 5) [18,192,33,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7932
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7933 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 300, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 194 37 268 50 45 77 141 269), lower := (rows 19 194 37 268 50 32 64 128 256), losses := [] }

theorem u7933 : Upper (D 5) (R 5) [18,192,33,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7933
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7934 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 37 268 52 43 75 139 267), lower := (rows 19 194 37 268 52 32 64 128 256), losses := [] }

theorem u7934 : Upper (D 5) (R 5) [18,192,33,260,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7934
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7935 : PairBound 9 := { available := 15, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 194 37 268 56 47 79 143 271), lower := (rows 19 194 37 268 56 32 64 128 256), losses := [] }

theorem u7935 : Upper (D 5) (R 5) [18,192,33,260,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7935
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7936 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 37 296 19 44 76 140 268), lower := (rows 19 194 37 296 19 32 64 128 256), losses := [] }

theorem u7936 : Upper (D 5) (R 5) [18,192,33,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7936
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7937 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 19 194 37 296 21 46 78 142 270), lower := (rows 19 194 37 296 21 32 64 128 256), losses := [] }

theorem u7937 : Upper (D 5) (R 5) [18,192,33,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7937
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7938 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 37 296 22 45 77 141 269), lower := (rows 19 194 37 296 22 32 64 128 256), losses := [] }

theorem u7938 : Upper (D 5) (R 5) [18,192,33,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7938
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7939 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 194 37 296 25 46 78 142 270), lower := (rows 19 194 37 296 25 32 64 128 256), losses := [] }

theorem u7939 : Upper (D 5) (R 5) [18,192,33,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7939
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7940 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 37 296 26 45 77 141 269), lower := (rows 19 194 37 296 26 32 64 128 256), losses := [] }

theorem u7940 : Upper (D 5) (R 5) [18,192,33,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7940
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7941 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 194 37 296 28 47 79 143 271), lower := (rows 19 194 37 296 28 32 64 128 256), losses := [] }

theorem u7941 : Upper (D 5) (R 5) [18,192,33,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7941
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7942 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 194 38 265 21 44 108 172 300), lower := (rows 19 194 38 265 21 32 64 128 256), losses := [] }

theorem u7942 : Upper (D 5) (R 5) [18,192,34,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7942
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7943 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 194 38 265 25 44 108 172 300), lower := (rows 19 194 38 265 25 32 64 128 256), losses := [] }

theorem u7943 : Upper (D 5) (R 5) [18,192,34,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7943
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7944 : Route 9 := (fun mask => (mask,id))

def c7944 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7944 : Upper (D 5) (R 5) [18,192,34,257,12] 13 := by
  apply FastRouting.sound _ _ [18,192,34,257,12] 13 (by decide) (choices 1) [1,4,8] r7944 c7944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4279
  · exact u4280
  · exact u4281

def b7945 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 17, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 194 38 265 49 44 76 140 268), lower := (rows 19 194 38 265 49 32 64 128 256), losses := [] }

theorem u7945 : Upper (D 5) (R 5) [18,192,34,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7945
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7946 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 194 38 265 52 45 77 141 269), lower := (rows 19 194 38 265 52 32 64 128 256), losses := [] }

theorem u7946 : Upper (D 5) (R 5) [18,192,34,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7946
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7947 : Route 9 := (fun mask => (mask,id))

def c7947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7947 : Upper (D 5) (R 5) [18,192,34,257,40] 13 := by
  apply FastRouting.sound _ _ [18,192,34,257,40] 13 (by decide) (choices 1) [1,4,8] r7947 c7947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4282
  · exact u4283
  · exact u4284

def b7948 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 194 38 268 21 41 105 169 297), lower := (rows 19 194 38 268 21 32 64 128 256), losses := [] }

theorem u7948 : Upper (D 5) (R 5) [18,192,34,260,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7948
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7949 : Route 9 := (fun mask => (mask,id))

def c7949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7949 : Upper (D 5) (R 5) [18,192,34,260,9] 13 := by
  apply FastRouting.sound _ _ [18,192,34,260,9] 13 (by decide) (choices 1) [1,4,8] r7949 c7949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4285
  · exact u4286
  · exact u4287

def b7950 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 38 268 28 41 105 169 297), lower := (rows 19 194 38 268 28 32 64 128 256), losses := [] }

theorem u7950 : Upper (D 5) (R 5) [18,192,34,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7950
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7951 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 17, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 194 38 268 49 45 77 141 269), lower := (rows 19 194 38 268 49 32 64 128 256), losses := [] }

theorem u7951 : Upper (D 5) (R 5) [18,192,34,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7951
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7952 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 194 38 268 52 41 73 137 265), lower := (rows 19 194 38 268 52 32 64 128 256), losses := [] }

theorem u7952 : Upper (D 5) (R 5) [18,192,34,260,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7952
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7953 : Route 9 := (fun mask => (mask,id))

def c7953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7953 : Upper (D 5) (R 5) [18,192,34,260,40] 13 := by
  apply FastRouting.sound _ _ [18,192,34,260,40] 13 (by decide) (choices 1) [1,4,8] r7953 c7953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4288
  · exact u4289
  · exact u4290

def b7954 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 194 38 296 21 45 77 141 269), lower := (rows 19 194 38 296 21 32 64 128 256), losses := [] }

theorem u7954 : Upper (D 5) (R 5) [18,192,34,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7954
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7955 : Route 9 := (fun mask => (mask,id))

def c7955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7955 : Upper (D 5) (R 5) [18,192,34,288,9] 13 := by
  apply FastRouting.sound _ _ [18,192,34,288,9] 13 (by decide) (choices 1) [1,4,8] r7955 c7955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4291
  · exact u4292
  · exact u4293

def b7956 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 194 38 296 28 45 77 141 269), lower := (rows 19 194 38 296 28 32 64 128 256), losses := [] }

theorem u7956 : Upper (D 5) (R 5) [18,192,34,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7956
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7957 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 44 265 19 44 108 172 300), lower := (rows 19 194 44 265 19 32 64 128 256), losses := [] }

theorem u7957 : Upper (D 5) (R 5) [18,192,40,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7957
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7958 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 230, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 194 44 265 21 46 110 174 302), lower := (rows 19 194 44 265 21 32 64 128 256), losses := [] }

theorem u7958 : Upper (D 5) (R 5) [18,192,40,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7958
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7959 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 44 265 22 45 109 173 301), lower := (rows 19 194 44 265 22 32 64 128 256), losses := [] }

theorem u7959 : Upper (D 5) (R 5) [18,192,40,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7959
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7960 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 194 44 265 25 38 102 166 294), lower := (rows 19 194 44 265 25 32 64 128 256), losses := [] }

theorem u7960 : Upper (D 5) (R 5) [18,192,40,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7960
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7961 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 44 265 26 37 101 165 293), lower := (rows 19 194 44 265 26 32 64 128 256), losses := [] }

theorem u7961 : Upper (D 5) (R 5) [18,192,40,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7961
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7962 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 44 265 28 39 103 167 295), lower := (rows 19 194 44 265 28 32 64 128 256), losses := [] }

theorem u7962 : Upper (D 5) (R 5) [18,192,40,257,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7962
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7963 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 230, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 194 44 265 49 46 78 142 270), lower := (rows 19 194 44 265 49 32 64 128 256), losses := [] }

theorem u7963 : Upper (D 5) (R 5) [18,192,40,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7963
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7964 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 44 265 50 45 77 141 269), lower := (rows 19 194 44 265 50 32 64 128 256), losses := [] }

theorem u7964 : Upper (D 5) (R 5) [18,192,40,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7964
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7965 : PairBound 9 := { available := 15, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 44 265 52 47 79 143 271), lower := (rows 19 194 44 265 52 32 64 128 256), losses := [] }

theorem u7965 : Upper (D 5) (R 5) [18,192,40,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7965
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7966 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 44 265 56 39 71 135 263), lower := (rows 19 194 44 265 56 32 64 128 256), losses := [] }

theorem u7966 : Upper (D 5) (R 5) [18,192,40,257,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7966
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7967 : Route 9 := (fun mask => (mask,id))

def c7967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7967 : Upper (D 5) (R 5) [18,192,40,258,5] 13 := by
  apply FastRouting.sound _ _ [18,192,40,258,5] 13 (by decide) (choices 1) [1,4,8] r7967 c7967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4294
  · exact u4295
  · exact u4296

def b7968 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 194 44 266 25 37 101 165 293), lower := (rows 19 194 44 266 25 32 64 128 256), losses := [] }

theorem u7968 : Upper (D 5) (R 5) [18,192,40,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7968
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7969 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 44 266 28 37 101 165 293), lower := (rows 19 194 44 266 28 32 64 128 256), losses := [] }

theorem u7969 : Upper (D 5) (R 5) [18,192,40,258,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7969
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7970 : Route 9 := (fun mask => (mask,id))

def c7970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7970 : Upper (D 5) (R 5) [18,192,40,258,33] 13 := by
  apply FastRouting.sound _ _ [18,192,40,258,33] 13 (by decide) (choices 1) [1,4,8] r7970 c7970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4297
  · exact u4298
  · exact u4299

def b7971 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 44 266 52 45 77 141 269), lower := (rows 19 194 44 266 52 32 64 128 256), losses := [] }

theorem u7971 : Upper (D 5) (R 5) [18,192,40,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7971
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7972 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 44 266 56 37 69 133 261), lower := (rows 19 194 44 266 56 32 64 128 256), losses := [] }

theorem u7972 : Upper (D 5) (R 5) [18,192,40,258,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7972
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7973 : PairBound 9 := { available := 45, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 44 268 19 45 109 173 301), lower := (rows 19 194 44 268 19 32 64 128 256), losses := [] }

theorem u7973 : Upper (D 5) (R 5) [18,192,40,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7973
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7974 : Route 9 := (fun mask => (mask,id))

def c7974 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7974 : Upper (D 5) (R 5) [18,192,40,260,5] 13 := by
  apply FastRouting.sound _ _ [18,192,40,260,5] 13 (by decide) (choices 1) [1,2,8] r7974 c7974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4300
  · exact u4301
  · exact u4302

def b7975 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 44 268 22 41 105 169 297), lower := (rows 19 194 44 268 22 32 64 128 256), losses := [] }

theorem u7975 : Upper (D 5) (R 5) [18,192,40,260,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7975
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7976 : Route 9 := (fun mask => (mask,id))

def c7976 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7976 : Upper (D 5) (R 5) [18,192,40,260,9] 13 := by
  apply FastRouting.sound _ _ [18,192,40,260,9] 13 (by decide) (choices 1) [1,2,4] r7976 c7976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4303
  · exact u4304
  · exact u4305

def b7977 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 44 268 26 37 101 165 293), lower := (rows 19 194 44 268 26 32 64 128 256), losses := [] }

theorem u7977 : Upper (D 5) (R 5) [18,192,40,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7977
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7978 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 227, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 44 268 28 35 99 163 291), lower := (rows 19 194 44 268 28 32 64 128 256), losses := [] }

theorem u7978 : Upper (D 5) (R 5) [18,192,40,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7978
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7979 : Route 9 := (fun mask => (mask,id))

def c7979 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7979 : Upper (D 5) (R 5) [18,192,40,260,33] 13 := by
  apply FastRouting.sound _ _ [18,192,40,260,33] 13 (by decide) (choices 1) [1,2,4,8] r7979 c7979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4306
  · exact u4307
  · exact u4308
  · exact u4309

#print axioms u7979
end Delivery.IrregularNine14.P05
