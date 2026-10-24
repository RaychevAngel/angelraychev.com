import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0017

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3960 : PairBound 9 := { available := 394, camps := [], pairs := [], upper := (rows 113 22 164 74 17 426 458 394 394), lower := (rows 113 22 164 74 17 32 64 128 256), losses := [] }

theorem u3960 : Upper (D 1) (R 1) [112,20,160,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3960
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3961 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 74 18 425 457 393 393), lower := (rows 113 22 164 74 18 32 64 128 256), losses := [] }

theorem u3961 : Upper (D 1) (R 1) [112,20,160,66,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3961
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3962 : PairBound 9 := { available := 387, camps := [], pairs := [], upper := (rows 113 22 164 74 24 419 451 387 387), lower := (rows 113 22 164 74 24 32 64 128 256), losses := [] }

theorem u3962 : Upper (D 1) (R 1) [112,20,160,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3962
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3963 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 164 74 144 299 331 395 267), lower := (rows 113 22 164 74 144 32 64 128 256), losses := [] }

theorem u3963 : Upper (D 1) (R 1) [112,20,160,66,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3963
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3964 : PairBound 9 := { available := 139, camps := [], pairs := [], upper := (rows 113 22 164 74 272 171 203 139 395), lower := (rows 113 22 164 74 272 32 64 128 256), losses := [] }

theorem u3964 : Upper (D 1) (R 1) [112,20,160,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3964
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3965 : PairBound 9 := { available := 330, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 137 18 362 330 458 330), lower := (rows 113 22 164 137 18 32 64 128 256), losses := [] }

theorem u3965 : Upper (D 1) (R 1) [112,20,160,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3965
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3966 : PairBound 9 := { available := 322, camps := [], pairs := [], upper := (rows 113 22 164 137 24 354 322 450 322), lower := (rows 113 22 164 137 24 32 64 128 256), losses := [] }

theorem u3966 : Upper (D 1) (R 1) [112,20,160,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3966
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3967 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 137 80 298 330 394 266), lower := (rows 113 22 164 137 80 32 64 128 256), losses := [] }

theorem u3967 : Upper (D 1) (R 1) [112,20,160,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3967
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3968 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 22 164 137 272 106 74 202 330), lower := (rows 113 22 164 137 272 32 64 128 256), losses := [] }

theorem u3968 : Upper (D 1) (R 1) [112,20,160,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3968
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3969 : PairBound 9 := { available := 266, camps := [], pairs := [], upper := (rows 113 22 164 200 17 298 330 394 266), lower := (rows 113 22 164 200 17 32 64 128 256), losses := [] }

theorem u3969 : Upper (D 1) (R 1) [112,20,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3969
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3970 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 200 18 299 331 395 267), lower := (rows 113 22 164 200 18 32 64 128 256), losses := [] }

theorem u3970 : Upper (D 1) (R 1) [112,20,160,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3970
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3971 : PairBound 9 := { available := 259, camps := [], pairs := [], upper := (rows 113 22 164 200 24 291 323 387 259), lower := (rows 113 22 164 200 24 32 64 128 256), losses := [] }

theorem u3971 : Upper (D 1) (R 1) [112,20,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3971
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3972 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 113 22 164 200 272 43 75 139 267), lower := (rows 113 22 164 200 272 32 64 128 256), losses := [] }

theorem u3972 : Upper (D 1) (R 1) [112,20,160,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3972
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3973 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 265 18 234 202 202 458), lower := (rows 113 22 164 265 18 32 64 128 256), losses := [] }

theorem u3973 : Upper (D 1) (R 1) [112,20,160,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3973
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3974 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 22 164 265 24 226 194 194 450), lower := (rows 113 22 164 265 24 32 64 128 256), losses := [] }

theorem u3974 : Upper (D 1) (R 1) [112,20,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3974
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3975 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 265 80 170 202 138 394), lower := (rows 113 22 164 265 80 32 64 128 256), losses := [] }

theorem u3975 : Upper (D 1) (R 1) [112,20,160,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3975
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3976 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 164 265 144 106 74 202 330), lower := (rows 113 22 164 265 144 32 64 128 256), losses := [] }

theorem u3976 : Upper (D 1) (R 1) [112,20,160,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3976
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3977 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 113 22 164 266 17 234 202 202 458), lower := (rows 113 22 164 266 17 32 64 128 256), losses := [] }

theorem u3977 : Upper (D 1) (R 1) [112,20,160,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3977
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3978 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 266 18 233 201 201 457), lower := (rows 113 22 164 266 18 32 64 128 256), losses := [] }

theorem u3978 : Upper (D 1) (R 1) [112,20,160,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3978
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3979 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 22 164 266 24 227 195 195 451), lower := (rows 113 22 164 266 24 32 64 128 256), losses := [] }

theorem u3979 : Upper (D 1) (R 1) [112,20,160,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3979
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3980 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 266 80 171 203 139 395), lower := (rows 113 22 164 266 80 32 64 128 256), losses := [] }

theorem u3980 : Upper (D 1) (R 1) [112,20,160,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3980
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3981 : PairBound 9 := { available := 75, camps := [{ cop := 1, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 164 266 144 107 75 203 331), lower := (rows 113 22 164 266 144 32 64 128 256), losses := [] }

theorem u3981 : Upper (D 1) (R 1) [112,20,160,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3981
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3982 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 113 22 164 328 17 170 202 138 394), lower := (rows 113 22 164 328 17 32 64 128 256), losses := [] }

theorem u3982 : Upper (D 1) (R 1) [112,20,160,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3982
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3983 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 328 18 171 203 139 395), lower := (rows 113 22 164 328 18 32 64 128 256), losses := [] }

theorem u3983 : Upper (D 1) (R 1) [112,20,160,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3983
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3984 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 22 164 328 24 163 195 131 387), lower := (rows 113 22 164 328 24 32 64 128 256), losses := [] }

theorem u3984 : Upper (D 1) (R 1) [112,20,160,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3984
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3985 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 164 328 144 43 75 139 267), lower := (rows 113 22 164 328 144 32 64 128 256), losses := [] }

theorem u3985 : Upper (D 1) (R 1) [112,20,160,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3985
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3986 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 22 164 392 17 106 74 202 330), lower := (rows 113 22 164 392 17 32 64 128 256), losses := [] }

theorem u3986 : Upper (D 1) (R 1) [112,20,160,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3986
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3987 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 392 18 107 75 203 331), lower := (rows 113 22 164 392 18 32 64 128 256), losses := [] }

theorem u3987 : Upper (D 1) (R 1) [112,20,160,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3987
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3988 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 22 164 392 24 99 67 195 323), lower := (rows 113 22 164 392 24 32 64 128 256), losses := [] }

theorem u3988 : Upper (D 1) (R 1) [112,20,160,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3988
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3989 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 392 80 43 75 139 267), lower := (rows 113 22 164 392 80 32 64 128 256), losses := [] }

theorem u3989 : Upper (D 1) (R 1) [112,20,160,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3989
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3990 : PairBound 9 := { available := 232, camps := [{ cop := 8, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 262 137 18 232 232 232 488), lower := (rows 113 22 262 137 18 32 64 128 256), losses := [] }

theorem u3990 : Upper (D 1) (R 1) [112,20,258,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3990
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3991 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 22 262 137 24 226 226 226 482), lower := (rows 113 22 262 137 24 32 64 128 256), losses := [] }

theorem u3991 : Upper (D 1) (R 1) [112,20,258,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3991
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3992 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 262 137 48 234 202 202 458), lower := (rows 113 22 262 137 48 32 64 128 256), losses := [] }

theorem u3992 : Upper (D 1) (R 1) [112,20,258,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3992
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3993 : Route 9 := (fun mask => (mask,id))

def c3993 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3993 : Upper (D 1) (R 1) [112,20,258,129,128] 13 := by
  apply FastRouting.sound _ _ [112,20,258,129,128] 13 (by decide) (choices 1) [2,8,64] r3993 c3993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1060
  · exact u1061
  · exact u1062

def b3994 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 113 22 262 168 17 234 202 202 458), lower := (rows 113 22 262 168 17 32 64 128 256), losses := [] }

theorem u3994 : Upper (D 1) (R 1) [112,20,258,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3994
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3995 : PairBound 9 := { available := 201, camps := [{ cop := 8, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 262 168 18 233 201 201 457), lower := (rows 113 22 262 168 18 32 64 128 256), losses := [] }

theorem u3995 : Upper (D 1) (R 1) [112,20,258,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3995
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3996 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 22 262 168 24 227 195 195 451), lower := (rows 113 22 262 168 24 32 64 128 256), losses := [] }

theorem u3996 : Upper (D 1) (R 1) [112,20,258,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3996
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3997 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 262 168 80 171 203 139 395), lower := (rows 113 22 262 168 80 32 64 128 256), losses := [] }

theorem u3997 : Upper (D 1) (R 1) [112,20,258,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3997
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3998 : Route 9 := (fun mask => (mask,id))

def c3998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3998 : Upper (D 1) (R 1) [112,20,258,160,128] 13 := by
  apply FastRouting.sound _ _ [112,20,258,160,128] 13 (by decide) (choices 1) [1,2,8,64] r3998 c3998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1063
  · exact u1064
  · exact u1065
  · exact u1066

def b3999 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 22 268 42 17 226 194 194 450), lower := (rows 113 22 268 42 17 32 64 128 256), losses := [] }

theorem u3999 : Upper (D 1) (R 1) [112,20,264,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3999
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4000 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 268 42 18 225 193 193 449), lower := (rows 113 22 268 42 18 32 64 128 256), losses := [] }

theorem u4000 : Upper (D 1) (R 1) [112,20,264,34,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4000
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4001 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 268 42 80 163 195 131 387), lower := (rows 113 22 268 42 80 32 64 128 256), losses := [] }

theorem u4001 : Upper (D 1) (R 1) [112,20,264,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4001
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4002 : Route 9 := (fun mask => (mask,id))

def c4002 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4002 : Upper (D 1) (R 1) [112,20,264,34,128] 13 := by
  apply FastRouting.sound _ _ [112,20,264,34,128] 13 (by decide) (choices 1) [1,2,64,128] r4002 c4002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1067
  · exact u1068
  · exact u1069
  · exact u1070

def b4003 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 268 137 18 226 226 226 482), lower := (rows 113 22 268 137 18 32 64 128 256), losses := [] }

theorem u4003 : Upper (D 1) (R 1) [112,20,264,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4003
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4004 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 268 137 48 226 194 194 450), lower := (rows 113 22 268 137 48 32 64 128 256), losses := [] }

theorem u4004 : Upper (D 1) (R 1) [112,20,264,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4004
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4005 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 268 137 144 98 98 226 354), lower := (rows 113 22 268 137 144 32 64 128 256), losses := [] }

theorem u4005 : Upper (D 1) (R 1) [112,20,264,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4005
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4006 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 22 268 138 17 226 226 226 482), lower := (rows 113 22 268 138 17 32 64 128 256), losses := [] }

theorem u4006 : Upper (D 1) (R 1) [112,20,264,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4006
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4007 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 268 138 18 225 225 225 481), lower := (rows 113 22 268 138 18 32 64 128 256), losses := [] }

theorem u4007 : Upper (D 1) (R 1) [112,20,264,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4007
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4008 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 268 138 48 227 195 195 451), lower := (rows 113 22 268 138 48 32 64 128 256), losses := [] }

theorem u4008 : Upper (D 1) (R 1) [112,20,264,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4008
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4009 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 268 138 144 99 99 227 355), lower := (rows 113 22 268 138 144 32 64 128 256), losses := [] }

theorem u4009 : Upper (D 1) (R 1) [112,20,264,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4009
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4010 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 22 268 168 17 226 194 194 450), lower := (rows 113 22 268 168 17 32 64 128 256), losses := [] }

theorem u4010 : Upper (D 1) (R 1) [112,20,264,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4010
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4011 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 268 168 18 227 195 195 451), lower := (rows 113 22 268 168 18 32 64 128 256), losses := [] }

theorem u4011 : Upper (D 1) (R 1) [112,20,264,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4011
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4012 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 268 168 80 163 195 131 387), lower := (rows 113 22 268 168 80 32 64 128 256), losses := [] }

theorem u4012 : Upper (D 1) (R 1) [112,20,264,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4012
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4013 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 268 168 144 99 67 195 323), lower := (rows 113 22 268 168 144 32 64 128 256), losses := [] }

theorem u4013 : Upper (D 1) (R 1) [112,20,264,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4013
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4014 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 113 22 292 74 17 170 202 138 394), lower := (rows 113 22 292 74 17 32 64 128 256), losses := [] }

theorem u4014 : Upper (D 1) (R 1) [112,20,288,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4014
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4015 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 292 74 18 169 201 137 393), lower := (rows 113 22 292 74 18 32 64 128 256), losses := [] }

theorem u4015 : Upper (D 1) (R 1) [112,20,288,66,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4015
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4016 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 22 292 74 24 163 195 131 387), lower := (rows 113 22 292 74 24 32 64 128 256), losses := [] }

theorem u4016 : Upper (D 1) (R 1) [112,20,288,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4016
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4017 : Route 9 := (fun mask => (mask,id))

def c4017 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4017 : Upper (D 1) (R 1) [112,20,288,66,128] 13 := by
  apply FastRouting.sound _ _ [112,20,288,66,128] 13 (by decide) (choices 1) [1,2,8,128] r4017 c4017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1071
  · exact u1072
  · exact u1073
  · exact u1074

def b4018 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 292 137 18 234 202 202 458), lower := (rows 113 22 292 137 18 32 64 128 256), losses := [] }

theorem u4018 : Upper (D 1) (R 1) [112,20,288,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4018
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4019 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 22 292 137 24 226 194 194 450), lower := (rows 113 22 292 137 24 32 64 128 256), losses := [] }

theorem u4019 : Upper (D 1) (R 1) [112,20,288,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4019
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4019
end Delivery.IrregularNine14.P01
