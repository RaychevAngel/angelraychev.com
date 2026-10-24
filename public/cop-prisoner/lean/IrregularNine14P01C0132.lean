import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0077

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7920 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 269 50 196 200 51 51 115 179 307), lower := (rows 269 50 196 200 16 32 64 128 256), losses := [] }

theorem u7920 : Upper (D 1) (R 1) [268,48,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7920
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7921 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 275 7 44 26 240 224 224 224 480), lower := (rows 275 7 44 26 16 32 64 128 256), losses := [] }

theorem u7921 : Upper (D 1) (R 1) [274,5,40,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7921
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7922 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 7 44 42 208 240 208 208 464), lower := (rows 275 7 44 42 16 32 64 128 256), losses := [] }

theorem u7922 : Upper (D 1) (R 1) [274,5,40,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7922
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7923 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 44 56 210 226 194 194 450), lower := (rows 275 7 44 56 16 32 64 128 256), losses := [] }

theorem u7923 : Upper (D 1) (R 1) [274,5,40,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7923
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7924 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 180, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 44 74 240 240 240 240 496), lower := (rows 275 7 44 74 16 32 64 128 256), losses := [] }

theorem u7924 : Upper (D 1) (R 1) [274,5,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7924
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7925 : Route 9 := (fun mask => (mask,id))

def c7925 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7925 : Upper (D 1) (R 1) [274,5,40,80] 13 := by
  apply FastRouting.sound _ _ [274,5,40,80] 13 (by decide) (choices 1) [2,32,64,128] r7925 c7925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4634
  · exact u4635
  · exact u4636
  · exact u4637

def b7926 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 44 104 210 242 210 210 466), lower := (rows 275 7 44 104 16 32 64 128 256), losses := [] }

theorem u7926 : Upper (D 1) (R 1) [274,5,40,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7926
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7927 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7927 : Upper (D 1) (R 1) [274,5,40,192] 13 := by
  apply FastRouting.sound _ _ [274,5,40,192] 13 (by decide) (choices 1) [2,32,64] r7927 c7927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4638
  · exact u4639
  · exact u4640

def b7928 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 275 7 100 26 248 232 232 232 488), lower := (rows 275 7 100 26 16 32 64 128 256), losses := [] }

theorem u7928 : Upper (D 1) (R 1) [274,5,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7928
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7929 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 212, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 100 42 216 248 216 216 472), lower := (rows 275 7 100 42 16 32 64 128 256), losses := [] }

theorem u7929 : Upper (D 1) (R 1) [274,5,96,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7929
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7930 : Route 9 := (fun mask => (mask,id))

def c7930 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7930 : Upper (D 1) (R 1) [274,5,96,48] 13 := by
  apply FastRouting.sound _ _ [274,5,96,48] 13 (by decide) (choices 1) [2,8,64,128] r7930 c7930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4641
  · exact u4642
  · exact u4643
  · exact u4644

def b7931 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 275 7 100 104 154 186 218 154 410), lower := (rows 275 7 100 104 16 32 64 128 256), losses := [] }

theorem u7931 : Upper (D 1) (R 1) [274,5,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7931
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7932 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 116, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 100 138 248 248 248 248 504), lower := (rows 275 7 100 138 16 32 64 128 256), losses := [] }

theorem u7932 : Upper (D 1) (R 1) [274,5,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7932
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7933 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7933 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7933 : Upper (D 1) (R 1) [274,5,96,144] 13 := by
  apply FastRouting.sound _ _ [274,5,96,144] 13 (by decide) (choices 1) [2,8,32,128] r7933 c7933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4645
  · exact u4646
  · exact u4647
  · exact u4648

def r7934 : Route 9 := (fun mask => (mask,id))

def c7934 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7934 : Upper (D 1) (R 1) [274,5,96,160] 13 := by
  apply FastRouting.sound _ _ [274,5,96,160] 13 (by decide) (choices 1) [2,8,64,128] r7934 c7934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4649
  · exact u4650
  · exact u4651
  · exact u4652

def b7935 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 14 7 104 240 240 240 240 496), lower := (rows 275 14 7 104 16 32 64 128 256), losses := [] }

theorem u7935 : Upper (D 1) (R 1) [274,12,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7935
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7936 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 14 21 104 242 226 226 226 482), lower := (rows 275 14 21 104 16 32 64 128 256), losses := [] }

theorem u7936 : Upper (D 1) (R 1) [274,12,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7936
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7937 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 14 22 41 240 224 224 224 480), lower := (rows 275 14 22 41 16 32 64 128 256), losses := [] }

theorem u7937 : Upper (D 1) (R 1) [274,12,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7937
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7938 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 14 22 104 241 225 225 225 481), lower := (rows 275 14 22 104 16 32 64 128 256), losses := [] }

theorem u7938 : Upper (D 1) (R 1) [274,12,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7938
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7939 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 275 14 37 42 208 240 208 208 464), lower := (rows 275 14 37 42 16 32 64 128 256), losses := [] }

theorem u7939 : Upper (D 1) (R 1) [274,12,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7939
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7940 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 275 14 37 56 210 226 194 194 450), lower := (rows 275 14 37 56 16 32 64 128 256), losses := [] }

theorem u7940 : Upper (D 1) (R 1) [274,12,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7940
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7941 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 275 14 37 74 240 240 240 240 496), lower := (rows 275 14 37 74 16 32 64 128 256), losses := [] }

theorem u7941 : Upper (D 1) (R 1) [274,12,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7941
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7942 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 275 14 37 88 242 226 226 226 482), lower := (rows 275 14 37 88 16 32 64 128 256), losses := [] }

theorem u7942 : Upper (D 1) (R 1) [274,12,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7942
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7943 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 14 37 104 210 242 210 210 466), lower := (rows 275 14 37 104 16 32 64 128 256), losses := [] }

theorem u7943 : Upper (D 1) (R 1) [274,12,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7943
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7944 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7944 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7944 : Upper (D 1) (R 1) [274,12,33,192] 13 := by
  apply FastRouting.sound _ _ [274,12,33,192] 13 (by decide) (choices 1) [2,32,64] r7944 c7944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4653
  · exact u4654
  · exact u4655

def b7945 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 275 14 38 104 209 241 209 209 465), lower := (rows 275 14 38 104 16 32 64 128 256), losses := [] }

theorem u7945 : Upper (D 1) (R 1) [274,12,34,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7945
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7946 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 275 14 38 200 241 241 241 241 497), lower := (rows 275 14 38 200 16 32 64 128 256), losses := [] }

theorem u7946 : Upper (D 1) (R 1) [274,12,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7946
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7947 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 275 14 52 104 211 227 195 195 451), lower := (rows 275 14 52 104 16 32 64 128 256), losses := [] }

theorem u7947 : Upper (D 1) (R 1) [274,12,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7947
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7948 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 275 14 52 200 243 227 227 227 483), lower := (rows 275 14 52 200 16 32 64 128 256), losses := [] }

theorem u7948 : Upper (D 1) (R 1) [274,12,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7948
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7949 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 275 14 100 104 147 179 211 147 403), lower := (rows 275 14 100 104 16 32 64 128 256), losses := [] }

theorem u7949 : Upper (D 1) (R 1) [274,12,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7949
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7950 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 14 100 168 211 243 211 211 467), lower := (rows 275 14 100 168 16 32 64 128 256), losses := [] }

theorem u7950 : Upper (D 1) (R 1) [274,12,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7950
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7951 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 14 28 240 224 224 224 480), lower := (rows 275 35 14 28 16 32 64 128 256), losses := [] }

theorem u7951 : Upper (D 1) (R 1) [274,33,10,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7951
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7952 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 275 35 14 44 208 240 208 208 464), lower := (rows 275 35 14 44 16 32 64 128 256), losses := [] }

theorem u7952 : Upper (D 1) (R 1) [274,33,10,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7952
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7953 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 275 35 14 56 212 228 196 196 452), lower := (rows 275 35 14 56 16 32 64 128 256), losses := [] }

theorem u7953 : Upper (D 1) (R 1) [274,33,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7953
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7954 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 275 35 14 76 240 240 240 240 496), lower := (rows 275 35 14 76 16 32 64 128 256), losses := [] }

theorem u7954 : Upper (D 1) (R 1) [274,33,10,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7954
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7955 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 275 35 14 88 244 228 228 228 484), lower := (rows 275 35 14 88 16 32 64 128 256), losses := [] }

theorem u7955 : Upper (D 1) (R 1) [274,33,10,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7955
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7956 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 275 35 14 104 212 244 212 212 468), lower := (rows 275 35 14 104 16 32 64 128 256), losses := [] }

theorem u7956 : Upper (D 1) (R 1) [274,33,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7956
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7957 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 275 35 14 200 244 244 244 244 500), lower := (rows 275 35 14 200 16 32 64 128 256), losses := [] }

theorem u7957 : Upper (D 1) (R 1) [274,33,10,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7957
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7958 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 22 44 216 232 200 200 456), lower := (rows 275 35 22 44 16 32 64 128 256), losses := [] }

theorem u7958 : Upper (D 1) (R 1) [274,33,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7958
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7959 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 22 76 248 232 232 232 488), lower := (rows 275 35 22 76 16 32 64 128 256), losses := [] }

theorem u7959 : Upper (D 1) (R 1) [274,33,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7959
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7960 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 22 104 220 236 204 204 460), lower := (rows 275 35 22 104 16 32 64 128 256), losses := [] }

theorem u7960 : Upper (D 1) (R 1) [274,33,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7960
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7961 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 22 200 252 236 236 236 492), lower := (rows 275 35 22 200 16 32 64 128 256), losses := [] }

theorem u7961 : Upper (D 1) (R 1) [274,33,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7961
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7962 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 35 28 42 212 228 196 196 452), lower := (rows 275 35 28 42 16 32 64 128 256), losses := [] }

theorem u7962 : Upper (D 1) (R 1) [274,33,24,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7962
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7963 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 28 44 210 226 194 194 450), lower := (rows 275 35 28 44 16 32 64 128 256), losses := [] }

theorem u7963 : Upper (D 1) (R 1) [274,33,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7963
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7964 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 180, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 28 74 244 228 228 228 484), lower := (rows 275 35 28 74 16 32 64 128 256), losses := [] }

theorem u7964 : Upper (D 1) (R 1) [274,33,24,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7964
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7965 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 28 76 242 226 226 226 482), lower := (rows 275 35 28 76 16 32 64 128 256), losses := [] }

theorem u7965 : Upper (D 1) (R 1) [274,33,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7965
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7966 : Route 9 := (fun mask => (mask,id))

def c7966 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7966 : Upper (D 1) (R 1) [274,33,24,96] 13 := by
  apply FastRouting.sound _ _ [274,33,24,96] 13 (by decide) (choices 1) [2,4,64,128] r7966 c7966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4656
  · exact u4657
  · exact u4658
  · exact u4659

def r7967 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7967 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u7967 : Upper (D 1) (R 1) [274,33,24,192] 13 := by
  apply FastRouting.sound _ _ [274,33,24,192] 13 (by decide) (choices 1) [2,4,32,64] r7967 c7967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4660
  · exact u4661
  · exact u4662
  · exact u4663

def b7968 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 35 38 76 216 248 216 216 472), lower := (rows 275 35 38 76 16 32 64 128 256), losses := [] }

theorem u7968 : Upper (D 1) (R 1) [274,33,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7968
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7969 : PairBound 9 := { available := 204, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 35 38 88 220 236 204 204 460), lower := (rows 275 35 38 88 16 32 64 128 256), losses := [] }

theorem u7969 : Upper (D 1) (R 1) [274,33,34,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7969
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7970 : PairBound 9 := { available := 220, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 35 38 200 220 252 220 220 476), lower := (rows 275 35 38 200 16 32 64 128 256), losses := [] }

theorem u7970 : Upper (D 1) (R 1) [274,33,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7970
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7971 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 180, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 44 74 212 244 212 212 468), lower := (rows 275 35 44 74 16 32 64 128 256), losses := [] }

theorem u7971 : Upper (D 1) (R 1) [274,33,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7971
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7972 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 35 44 76 210 242 210 210 466), lower := (rows 275 35 44 76 16 32 64 128 256), losses := [] }

theorem u7972 : Upper (D 1) (R 1) [274,33,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7972
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7973 : Route 9 := (fun mask => (mask,id))

def c7973 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7973 : Upper (D 1) (R 1) [274,33,40,80] 13 := by
  apply FastRouting.sound _ _ [274,33,40,80] 13 (by decide) (choices 1) [2,4,64,128] r7973 c7973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4664
  · exact u4665
  · exact u4666
  · exact u4667

def r7974 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7974 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7974 : Upper (D 1) (R 1) [274,33,40,192] 13 := by
  apply FastRouting.sound _ _ [274,33,40,192] 13 (by decide) (choices 1) [2,4,64] r7974 c7974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4668
  · exact u4669
  · exact u4670

def b7975 : PairBound 9 := { available := 204, camps := [{ cop := 3, region := 180, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 52 74 220 236 204 204 460), lower := (rows 275 35 52 74 16 32 64 128 256), losses := [] }

theorem u7975 : Upper (D 1) (R 1) [274,33,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7975
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7976 : Route 9 := (fun mask => (mask,id))

def c7976 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7976 : Upper (D 1) (R 1) [274,33,48,68] 13 := by
  apply FastRouting.sound _ _ [274,33,48,68] 13 (by decide) (choices 1) [2,8,64,128] r7976 c7976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4671
  · exact u4672
  · exact u4673
  · exact u4674

def r7977 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7977 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 256 => 8 | _ => 0)

theorem u7977 : Upper (D 1) (R 1) [274,33,48,192] 13 := by
  apply FastRouting.sound _ _ [274,33,48,192] 13 (by decide) (choices 1) [2,4,8,64] r7977 c7977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4675
  · exact u4676
  · exact u4677
  · exact u4678

def b7978 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 35 70 76 184 184 248 184 440), lower := (rows 275 35 70 76 16 32 64 128 256), losses := [] }

theorem u7978 : Upper (D 1) (R 1) [274,33,66,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7978
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7979 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 184, targets := 2 }], pairs := [(3,1)], upper := (rows 275 35 70 88 188 172 236 172 428), lower := (rows 275 35 70 88 16 32 64 128 256), losses := [] }

theorem u7979 : Upper (D 1) (R 1) [274,33,66,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7979
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u7979
end Delivery.IrregularNine14.P01
