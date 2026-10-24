import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0026

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3960 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 28 137 148 97 97 225 353), lower := (rows 35 322 28 137 148 32 64 128 256), losses := [] }

theorem u3960 : Upper (D 3) (R 3) [34,320,24,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3960
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3961 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 28 137 176 101 69 197 325), lower := (rows 35 322 28 137 176 32 64 128 256), losses := [] }

theorem u3961 : Upper (D 3) (R 3) [34,320,24,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3961
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3962 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 28 137 208 37 101 165 293), lower := (rows 35 322 28 137 208 32 64 128 256), losses := [] }

theorem u3962 : Upper (D 3) (R 3) [34,320,24,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3962
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3963 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 28 140 176 97 65 193 321), lower := (rows 35 322 28 140 176 32 64 128 256), losses := [] }

theorem u3963 : Upper (D 3) (R 3) [34,320,24,132,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3963
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3964 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 28 140 208 33 97 161 289), lower := (rows 35 322 28 140 208 32 64 128 256), losses := [] }

theorem u3964 : Upper (D 3) (R 3) [34,320,24,132,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3964
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3965 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 28 168 208 37 69 133 261), lower := (rows 35 322 28 168 208 32 64 128 256), losses := [] }

theorem u3965 : Upper (D 3) (R 3) [34,320,24,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3965
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3966 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 37 76 145 185 217 153 409), lower := (rows 35 322 37 76 145 32 64 128 256), losses := [] }

theorem u3966 : Upper (D 3) (R 3) [34,320,33,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3966
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3967 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 37 76 152 177 209 145 401), lower := (rows 35 322 37 76 152 32 64 128 256), losses := [] }

theorem u3967 : Upper (D 3) (R 3) [34,320,33,68,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3967
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3968 : PairBound 9 := { available := 141, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 37 88 145 173 205 141 397), lower := (rows 35 322 37 88 145 32 64 128 256), losses := [] }

theorem u3968 : Upper (D 3) (R 3) [34,320,33,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3968
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3969 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 37 88 148 169 201 137 393), lower := (rows 35 322 37 88 148 32 64 128 256), losses := [] }

theorem u3969 : Upper (D 3) (R 3) [34,320,33,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3969
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3970 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 37 137 148 121 89 217 345), lower := (rows 35 322 37 137 148 32 64 128 256), losses := [] }

theorem u3970 : Upper (D 3) (R 3) [34,320,33,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3970
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3971 : PairBound 9 := { available := 29, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 37 137 208 61 93 157 285), lower := (rows 35 322 37 137 208 32 64 128 256), losses := [] }

theorem u3971 : Upper (D 3) (R 3) [34,320,33,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3971
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3972 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 37 140 208 57 89 153 281), lower := (rows 35 322 37 140 208 32 64 128 256), losses := [] }

theorem u3972 : Upper (D 3) (R 3) [34,320,33,132,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3972
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3973 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 44 73 145 181 213 149 405), lower := (rows 35 322 44 73 145 32 64 128 256), losses := [] }

theorem u3973 : Upper (D 3) (R 3) [34,320,40,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3973
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3974 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 44 73 148 177 209 145 401), lower := (rows 35 322 44 73 148 32 64 128 256), losses := [] }

theorem u3974 : Upper (D 3) (R 3) [34,320,40,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3974
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3975 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 44 76 145 177 209 145 401), lower := (rows 35 322 44 76 145 32 64 128 256), losses := [] }

theorem u3975 : Upper (D 3) (R 3) [34,320,40,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3975
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3976 : Route 9 := (fun mask => (mask,id))

def c3976 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3976 : Upper (D 3) (R 3) [34,320,40,80,129] 13 := by
  apply FastRouting.sound _ _ [34,320,40,80,129] 13 (by decide) (choices 1) [1,4,128] r3976 c3976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1585
  · exact u1586
  · exact u1587

def b3977 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 44 88 148 161 193 129 385), lower := (rows 35 322 44 88 148 32 64 128 256), losses := [] }

theorem u3977 : Upper (D 3) (R 3) [34,320,40,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3977
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3978 : PairBound 9 := { available := 149, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 44 137 81 181 213 149 405), lower := (rows 35 322 44 137 81 32 64 128 256), losses := [] }

theorem u3978 : Upper (D 3) (R 3) [34,320,40,129,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3978
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3979 : Route 9 := (fun mask => (mask,id))

def c3979 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3979 : Upper (D 3) (R 3) [34,320,40,129,68] 13 := by
  apply FastRouting.sound _ _ [34,320,40,129,68] 13 (by decide) (choices 1) [1,16,128] r3979 c3979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1588
  · exact u1589
  · exact u1590

def b3980 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 322 44 137 145 117 85 213 341), lower := (rows 35 322 44 137 145 32 64 128 256), losses := [] }

theorem u3980 : Upper (D 3) (R 3) [34,320,40,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3980
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3981 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 137 148 113 81 209 337), lower := (rows 35 322 44 137 148 32 64 128 256), losses := [] }

theorem u3981 : Upper (D 3) (R 3) [34,320,40,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3981
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3982 : Route 9 := (fun mask => (mask,id))

def c3982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3982 : Upper (D 3) (R 3) [34,320,40,129,192] 13 := by
  apply FastRouting.sound _ _ [34,320,40,129,192] 13 (by decide) (choices 1) [1,4,16] r3982 c3982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1591
  · exact u1592
  · exact u1593

def b3983 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 44 140 145 113 81 209 337), lower := (rows 35 322 44 140 145 32 64 128 256), losses := [] }

theorem u3983 : Upper (D 3) (R 3) [34,320,40,132,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3983
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3984 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 44 140 208 49 81 145 273), lower := (rows 35 322 44 140 208 32 64 128 256), losses := [] }

theorem u3984 : Upper (D 3) (R 3) [34,320,40,132,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3984
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3985 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 44 152 81 165 197 133 389), lower := (rows 35 322 44 152 81 32 64 128 256), losses := [] }

theorem u3985 : Upper (D 3) (R 3) [34,320,40,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3985
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3986 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 44 152 84 161 193 129 385), lower := (rows 35 322 44 152 84 32 64 128 256), losses := [] }

theorem u3986 : Upper (D 3) (R 3) [34,320,40,144,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3986
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3987 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 152 145 101 69 197 325), lower := (rows 35 322 44 152 145 32 64 128 256), losses := [] }

theorem u3987 : Upper (D 3) (R 3) [34,320,40,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3987
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3988 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 152 148 97 65 193 321), lower := (rows 35 322 44 152 148 32 64 128 256), losses := [] }

theorem u3988 : Upper (D 3) (R 3) [34,320,40,144,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3988
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3989 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 152 208 37 69 133 261), lower := (rows 35 322 44 152 208 32 64 128 256), losses := [] }

theorem u3989 : Upper (D 3) (R 3) [34,320,40,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3989
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3990 : Route 9 := (fun mask => (mask,id))

def c3990 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3990 : Upper (D 3) (R 3) [34,320,40,192,129] 13 := by
  apply FastRouting.sound _ _ [34,320,40,192,129] 13 (by decide) (choices 1) [1,4,16] r3990 c3990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1594
  · exact u1595
  · exact u1596

def b3991 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 200 148 49 81 145 273), lower := (rows 35 322 44 200 148 32 64 128 256), losses := [] }

theorem u3991 : Upper (D 3) (R 3) [34,320,40,192,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3991
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3992 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 69 137 148 57 121 185 313), lower := (rows 35 322 69 137 148 32 64 128 256), losses := [] }

theorem u3992 : Upper (D 3) (R 3) [34,320,65,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3992
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3993 : PairBound 9 := { available := 29, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 69 137 176 61 93 157 285), lower := (rows 35 322 69 137 176 32 64 128 256), losses := [] }

theorem u3993 : Upper (D 3) (R 3) [34,320,65,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3993
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3994 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 69 140 176 57 89 153 281), lower := (rows 35 322 69 140 176 32 64 128 256), losses := [] }

theorem u3994 : Upper (D 3) (R 3) [34,320,65,132,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3994
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3995 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 322 76 137 145 53 117 181 309), lower := (rows 35 322 76 137 145 32 64 128 256), losses := [] }

theorem u3995 : Upper (D 3) (R 3) [34,320,72,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3995
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3996 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 76 137 148 49 113 177 305), lower := (rows 35 322 76 137 148 32 64 128 256), losses := [] }

theorem u3996 : Upper (D 3) (R 3) [34,320,72,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3996
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3997 : Route 9 := (fun mask => (mask,id))

def c3997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3997 : Upper (D 3) (R 3) [34,320,72,129,160] 13 := by
  apply FastRouting.sound _ _ [34,320,72,129,160] 13 (by decide) (choices 1) [1,4,16] r3997 c3997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1597
  · exact u1598
  · exact u1599

def b3998 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 76 140 145 49 113 177 305), lower := (rows 35 322 76 140 145 32 64 128 256), losses := [] }

theorem u3998 : Upper (D 3) (R 3) [34,320,72,132,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3998
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3999 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 76 140 176 49 81 145 273), lower := (rows 35 322 76 140 176 32 64 128 256), losses := [] }

theorem u3999 : Upper (D 3) (R 3) [34,320,72,132,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3999
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4000 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 76 152 145 37 101 165 293), lower := (rows 35 322 76 152 145 32 64 128 256), losses := [] }

theorem u4000 : Upper (D 3) (R 3) [34,320,72,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4000
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4001 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 76 152 148 33 97 161 289), lower := (rows 35 322 76 152 148 32 64 128 256), losses := [] }

theorem u4001 : Upper (D 3) (R 3) [34,320,72,144,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4001
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4002 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 76 152 176 37 69 133 261), lower := (rows 35 322 76 152 176 32 64 128 256), losses := [] }

theorem u4002 : Upper (D 3) (R 3) [34,320,72,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4002
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4003 : Route 9 := (fun mask => (mask,id))

def c4003 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4003 : Upper (D 3) (R 3) [34,320,72,160,129] 13 := by
  apply FastRouting.sound _ _ [34,320,72,160,129] 13 (by decide) (choices 1) [1,4,16] r4003 c4003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1600
  · exact u1601
  · exact u1602

def b4004 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 76 168 148 49 81 145 273), lower := (rows 35 322 76 168 148 32 64 128 256), losses := [] }

theorem u4004 : Upper (D 3) (R 3) [34,320,72,160,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4004
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4005 : PairBound 9 := { available := 29, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 322 100 137 145 61 93 157 285), lower := (rows 35 322 100 137 145 32 64 128 256), losses := [] }

theorem u4005 : Upper (D 3) (R 3) [34,320,96,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4005
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4006 : Route 9 := (fun mask => (mask,id))

def c4006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4006 : Upper (D 3) (R 3) [34,320,96,129,132] 13 := by
  apply FastRouting.sound _ _ [34,320,96,129,132] 13 (by decide) (choices 1) [1,8,16] r4006 c4006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1603
  · exact u1604
  · exact u1605

def b4007 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 322 100 137 152 53 85 149 277), lower := (rows 35 322 100 137 152 32 64 128 256), losses := [] }

theorem u4007 : Upper (D 3) (R 3) [34,320,96,129,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4007
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4008 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 322 100 140 152 49 81 145 273), lower := (rows 35 322 100 140 152 32 64 128 256), losses := [] }

theorem u4008 : Upper (D 3) (R 3) [34,320,96,132,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4008
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4009 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 322 100 152 152 37 69 133 261), lower := (rows 35 322 100 152 152 32 64 128 256), losses := [] }

theorem u4009 : Upper (D 3) (R 3) [34,320,96,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4009
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4010 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 25 152 480 480 480 480), lower := (rows 97 7 7 25 152 32 64 128 256), losses := [] }

theorem u4010 : Upper (D 3) (R 3) [96,5,3,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4010
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4011 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 25 280 224 224 224 480), lower := (rows 97 7 7 25 280 32 64 128 256), losses := [] }

theorem u4011 : Upper (D 3) (R 3) [96,5,3,17,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4011
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4012 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 25 400 232 232 232 488), lower := (rows 97 7 7 25 400 32 64 128 256), losses := [] }

theorem u4012 : Upper (D 3) (R 3) [96,5,3,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4012
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4013 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 56 145 488 456 456 456), lower := (rows 97 7 7 56 145 32 64 128 256), losses := [] }

theorem u4013 : Upper (D 3) (R 3) [96,5,3,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4013
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4014 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 56 208 425 457 393 393), lower := (rows 97 7 7 56 208 32 64 128 256), losses := [] }

theorem u4014 : Upper (D 3) (R 3) [96,5,3,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4014
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4015 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 56 273 232 200 200 456), lower := (rows 97 7 7 56 273 32 64 128 256), losses := [] }

theorem u4015 : Upper (D 3) (R 3) [96,5,3,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4015
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4016 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 56 336 169 201 137 393), lower := (rows 97 7 7 56 336 32 64 128 256), losses := [] }

theorem u4016 : Upper (D 3) (R 3) [96,5,3,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4016
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4017 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 56 400 233 201 201 457), lower := (rows 97 7 7 56 400 32 64 128 256), losses := [] }

theorem u4017 : Upper (D 3) (R 3) [96,5,3,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4017
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4018 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 137 176 376 344 472 344), lower := (rows 97 7 7 137 176 32 64 128 256), losses := [] }

theorem u4018 : Upper (D 3) (R 3) [96,5,3,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4018
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4019 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 137 280 240 240 240 496), lower := (rows 97 7 7 137 280 32 64 128 256), losses := [] }

theorem u4019 : Upper (D 3) (R 3) [96,5,3,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4019
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4019
end Delivery.IrregularNine14.P03
