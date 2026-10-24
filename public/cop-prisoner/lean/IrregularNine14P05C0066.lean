import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0021
import IrregularNine14P05C0022

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3960 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 44 140 304 40 67 131 259), lower := (rows 19 70 44 140 304 40 64 128 256), losses := [] }

theorem u3960 : Upper (D 5) (R 5) [18,68,40,132,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3960
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3961 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 44 392 25 33 102 166 294), lower := (rows 19 70 44 392 25 33 64 128 256), losses := [] }

theorem u3961 : Upper (D 5) (R 5) [18,68,40,384,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3961
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3962 : Route 9 := (fun mask => (mask,id))

def c3962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3962 : Upper (D 5) (R 5) [18,68,40,384,9,2] 13 := by
  apply FastRouting.sound _ _ [18,68,40,384,9,2] 13 (by decide) (choices 1) [1,4,32] r3962 c3962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1298
  · exact u1299
  · exact u1300

def b3963 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 44 392 25 36 99 163 291), lower := (rows 19 70 44 392 25 36 64 128 256), losses := [] }

theorem u3963 : Upper (D 5) (R 5) [18,68,40,384,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3963
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3964 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 392 49 33 78 142 270), lower := (rows 19 70 44 392 49 33 64 128 256), losses := [] }

theorem u3964 : Upper (D 5) (R 5) [18,68,40,384,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3964
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3965 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 392 49 34 77 141 269), lower := (rows 19 70 44 392 49 34 64 128 256), losses := [] }

theorem u3965 : Upper (D 5) (R 5) [18,68,40,384,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3965
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3966 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 392, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 19 70 44 392 49 36 75 139 267), lower := (rows 19 70 44 392 49 36 64 128 256), losses := [] }

theorem u3966 : Upper (D 5) (R 5) [18,68,40,384,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3966
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3967 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 83, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 70 44 392 49 40 71 135 263), lower := (rows 19 70 44 392 49 40 64 128 256), losses := [] }

theorem u3967 : Upper (D 5) (R 5) [18,68,40,384,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3967
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3968 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 19 70 133 41 276 34 104 168 296), lower := (rows 19 70 133 41 276 34 64 128 256), losses := [] }

theorem u3968 : Upper (D 5) (R 5) [18,68,129,33,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3968
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3969 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 40, targets := 2 },{ cop := 0, region := 40, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 133 41 276 40 106 170 298), lower := (rows 19 70 133 41 276 40 64 128 256), losses := [] }

theorem u3969 : Upper (D 5) (R 5) [18,68,129,33,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3969
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3970 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 19 70 133 41 280 34 108 172 300), lower := (rows 19 70 133 41 280 34 64 128 256), losses := [] }

theorem u3970 : Upper (D 5) (R 5) [18,68,129,33,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3970
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3971 : Route 9 := (fun mask => (mask,id))

def c3971 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3971 : Upper (D 5) (R 5) [18,68,129,33,264,4] 13 := by
  apply FastRouting.sound _ _ [18,68,129,33,264,4] 13 (by decide) (choices 1) [2,8,32] r3971 c3971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1301
  · exact u1302
  · exact u1303

def b3972 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 133 41 280 40 102 166 294), lower := (rows 19 70 133 41 280 40 64 128 256), losses := [] }

theorem u3972 : Upper (D 5) (R 5) [18,68,129,33,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3972
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3973 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 40, targets := 4 }], pairs := [(1,0),(3,2)], upper := (rows 19 70 133 42 28 33 360 424 296), lower := (rows 19 70 133 42 28 33 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 72 136 264), good := (rows 18 70 132 490 478 32 64 128 256) }] }

theorem u3973 : Upper (D 5) (R 5) [18,68,129,34,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3973
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3974 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 70 133 42 28 40 353 417 289), lower := (rows 19 70 133 42 28 40 64 128 256), losses := [] }

theorem u3974 : Upper (D 5) (R 5) [18,68,129,34,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3974
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3975 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(3,2)], upper := (rows 19 70 133 42 28 288 105 169 297), lower := (rows 19 70 133 42 28 288 64 128 256), losses := [] }

theorem u3975 : Upper (D 5) (R 5) [18,68,129,34,12,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3975
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3976 : PairBound 9 := { available := 264, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 133 42 52 33 328 392 264), lower := (rows 19 70 133 42 52 33 64 128 256), losses := [] }

theorem u3976 : Upper (D 5) (R 5) [18,68,129,34,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3976
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3977 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 70 133 42 52 40 329 393 265), lower := (rows 19 70 133 42 52 40 64 128 256), losses := [] }

theorem u3977 : Upper (D 5) (R 5) [18,68,129,34,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3977
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3978 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(3,2)], upper := (rows 19 70 133 42 52 288 73 137 265), lower := (rows 19 70 133 42 52 288 64 128 256), losses := [] }

theorem u3978 : Upper (D 5) (R 5) [18,68,129,34,36,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3978
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3979 : Route 9 := (fun mask => (mask,id))

def c3979 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3979 : Upper (D 5) (R 5) [18,68,129,34,260,1] 13 := by
  apply FastRouting.sound _ _ [18,68,129,34,260,1] 13 (by decide) (choices 1) [8,32] r3979 c3979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1304
  · exact u1305

def b3980 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 70 133 42 276 40 105 169 297), lower := (rows 19 70 133 42 276 40 64 128 256), losses := [] }

theorem u3980 : Upper (D 5) (R 5) [18,68,129,34,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3980
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3981 : Route 9 := (fun mask => (mask,id))

def c3981 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3981 : Upper (D 5) (R 5) [18,68,129,34,264,1] 13 := by
  apply FastRouting.sound _ _ [18,68,129,34,264,1] 13 (by decide) (choices 1) [4,8,32] r3981 c3981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1306
  · exact u1307
  · exact u1308

def b3982 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 273, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 133 42 280 36 105 169 297), lower := (rows 19 70 133 42 280 36 64 128 256), losses := [] }

theorem u3982 : Upper (D 5) (R 5) [18,68,129,34,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3982
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3983 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 70 133 42 280 40 101 165 293), lower := (rows 19 70 133 42 280 40 64 128 256), losses := [] }

theorem u3983 : Upper (D 5) (R 5) [18,68,129,34,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3983
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3984 : Route 9 := (fun mask => (mask,id))

def c3984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3984 : Upper (D 5) (R 5) [18,68,129,34,288,1] 13 := by
  apply FastRouting.sound _ _ [18,68,129,34,288,1] 13 (by decide) (choices 1) [4,8] r3984 c3984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1309
  · exact u1310

def b3985 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 273, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 133 42 304 36 73 137 265), lower := (rows 19 70 133 42 304 36 64 128 256), losses := [] }

theorem u3985 : Upper (D 5) (R 5) [18,68,129,34,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3985
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3986 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 70 133 42 304 40 77 141 269), lower := (rows 19 70 133 42 304 40 64 128 256), losses := [] }

theorem u3986 : Upper (D 5) (R 5) [18,68,129,34,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3986
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3987 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 338, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 19 70 133 44 280 33 106 170 298), lower := (rows 19 70 133 44 280 33 64 128 256), losses := [] }

theorem u3987 : Upper (D 5) (R 5) [18,68,129,36,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3987
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3988 : Route 9 := (fun mask => (mask,id))

def c3988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3988 : Upper (D 5) (R 5) [18,68,129,36,264,2] 13 := by
  apply FastRouting.sound _ _ [18,68,129,36,264,2] 13 (by decide) (choices 1) [1,8,32] r3988 c3988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1311
  · exact u1312
  · exact u1313

def b3989 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 133 44 280 40 99 163 291), lower := (rows 19 70 133 44 280 40 64 128 256), losses := [] }

theorem u3989 : Upper (D 5) (R 5) [18,68,129,36,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3989
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3990 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 338, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 19 70 133 44 304 33 74 138 266), lower := (rows 19 70 133 44 304 33 64 128 256), losses := [] }

theorem u3990 : Upper (D 5) (R 5) [18,68,129,36,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3990
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3991 : Route 9 := (fun mask => (mask,id))

def c3991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3991 : Upper (D 5) (R 5) [18,68,129,36,288,2] 13 := by
  apply FastRouting.sound _ _ [18,68,129,36,288,2] 13 (by decide) (choices 1) [1,8] r3991 c3991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1314
  · exact u1315

def b3992 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 133 44 304 40 75 139 267), lower := (rows 19 70 133 44 304 40 64 128 256), losses := [] }

theorem u3992 : Upper (D 5) (R 5) [18,68,129,36,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3992
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3993 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 133 265 52 34 104 168 296), lower := (rows 19 70 133 265 52 34 64 128 256), losses := [] }

theorem u3993 : Upper (D 5) (R 5) [18,68,129,257,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3993
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3994 : Route 9 := (fun mask => (mask,id))

def c3994 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3994 : Upper (D 5) (R 5) [18,68,129,257,36,8] 13 := by
  apply FastRouting.sound _ _ [18,68,129,257,36,8] 13 (by decide) (choices 1) [2,8,32] r3994 c3994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1316
  · exact u1317
  · exact u1318

def b3995 : PairBound 9 := { available := 44, camps := [], pairs := [(4,0),(4,2)], upper := (rows 19 70 133 265 56 34 108 172 300), lower := (rows 19 70 133 265 56 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 35 64 128 256), good := (rows 50 102 164 312 56 34 64 128 256) },{ target := 2, region := (rows 1 2 0 8 24 35 64 128 256), good := (rows 51 98 161 313 56 34 64 128 256) }] }

theorem u3995 : Upper (D 5) (R 5) [18,68,129,257,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3995
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3996 : Route 9 := (fun mask => (mask,id))

def c3996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3996 : Upper (D 5) (R 5) [18,68,129,257,40,4] 13 := by
  apply FastRouting.sound _ _ [18,68,129,257,40,4] 13 (by decide) (choices 1) [2,8,32] r3996 c3996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1319
  · exact u1320
  · exact u1321

def b3997 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 133 265 56 40 102 166 294), lower := (rows 19 70 133 265 56 40 64 128 256), losses := [] }

theorem u3997 : Upper (D 5) (R 5) [18,68,129,257,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3997
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3998 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(2,1),(3,2)], upper := (rows 19 70 133 266 28 33 104 168 296), lower := (rows 19 70 133 266 28 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 37 80 144 272), good := (rows 501 100 165 264 508 37 64 128 256) }] }

theorem u3998 : Upper (D 5) (R 5) [18,68,129,258,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3998
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3999 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(2,1),(3,2)], upper := (rows 19 70 133 266 28 40 97 161 289), lower := (rows 19 70 133 266 28 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 56 65 129 257), good := (rows 501 68 453 296 60 40 64 128 256) }] }

theorem u3999 : Upper (D 5) (R 5) [18,68,129,258,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3999
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4000 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 133 266 52 33 104 168 296), lower := (rows 19 70 133 266 52 33 64 128 256), losses := [] }

theorem u4000 : Upper (D 5) (R 5) [18,68,129,258,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4000
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4001 : Route 9 := (fun mask => (mask,id))

def c4001 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4001 : Upper (D 5) (R 5) [18,68,129,258,36,8] 13 := by
  apply FastRouting.sound _ _ [18,68,129,258,36,8] 13 (by decide) (choices 1) [1,8,32] r4001 c4001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1322
  · exact u1323
  · exact u1324

def b4002 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 133 266 56 33 108 172 300), lower := (rows 19 70 133 266 56 33 64 128 256), losses := [] }

theorem u4002 : Upper (D 5) (R 5) [18,68,129,258,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4002
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4003 : PairBound 9 := { available := 41, camps := [], pairs := [(4,0),(4,1)], upper := (rows 19 70 133 266 56 36 105 169 297), lower := (rows 19 70 133 266 56 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 38 64 128 256), good := (rows 50 102 164 314 56 36 64 128 256) },{ target := 1, region := (rows 1 0 4 8 24 38 64 128 256), good := (rows 49 100 165 312 56 36 64 128 256) }] }

theorem u4003 : Upper (D 5) (R 5) [18,68,129,258,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4003
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4004 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 70 133 266 56 40 101 165 293), lower := (rows 19 70 133 266 56 40 64 128 256), losses := [] }

theorem u4004 : Upper (D 5) (R 5) [18,68,129,258,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4004
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4005 : PairBound 9 := { available := 42, camps := [], pairs := [(4,1),(4,2)], upper := (rows 19 70 133 268 56 33 106 170 298), lower := (rows 19 70 133 268 56 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 37 64 128 256), good := (rows 49 100 165 316 56 33 64 128 256) },{ target := 2, region := (rows 1 2 0 8 24 37 64 128 256), good := (rows 51 98 161 312 56 33 64 128 256) }] }

theorem u4005 : Upper (D 5) (R 5) [18,68,129,260,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4005
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4006 : Route 9 := (fun mask => (mask,id))

def c4006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4006 : Upper (D 5) (R 5) [18,68,129,260,40,2] 13 := by
  apply FastRouting.sound _ _ [18,68,129,260,40,2] 13 (by decide) (choices 1) [1,8,32] r4006 c4006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1325
  · exact u1326
  · exact u1327

def b4007 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 133 268 56 40 99 163 291), lower := (rows 19 70 133 268 56 40 64 128 256), losses := [] }

theorem u4007 : Upper (D 5) (R 5) [18,68,129,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4007
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4008 : Route 9 := (fun mask => (mask,id))

def c4008 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4008 : Upper (D 5) (R 5) [18,68,129,288,12,1] 13 := by
  apply FastRouting.sound _ _ [18,68,129,288,12,1] 13 (by decide) (choices 1) [2,8,32] r4008 c4008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1328
  · exact u1329
  · exact u1330

def r4009 : Route 9 := (fun mask => (mask,id))

def c4009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4009 : Upper (D 5) (R 5) [18,68,129,288,12,2] 13 := by
  apply FastRouting.sound _ _ [18,68,129,288,12,2] 13 (by decide) (choices 1) [1,8,32] r4009 c4009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1331
  · exact u1332
  · exact u1333

def b4010 : PairBound 9 := { available := 35, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 133 296 28 40 99 163 291), lower := (rows 19 70 133 296 28 40 64 128 256), losses := [] }

theorem u4010 : Upper (D 5) (R 5) [18,68,129,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4010
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4011 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 133 296 52 33 74 138 266), lower := (rows 19 70 133 296 52 33 64 128 256), losses := [] }

theorem u4011 : Upper (D 5) (R 5) [18,68,129,288,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4011
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4012 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 133 296 52 34 73 137 265), lower := (rows 19 70 133 296 52 34 64 128 256), losses := [] }

theorem u4012 : Upper (D 5) (R 5) [18,68,129,288,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4012
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4013 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 133 296 52 40 75 139 267), lower := (rows 19 70 133 296 52 40 64 128 256), losses := [] }

theorem u4013 : Upper (D 5) (R 5) [18,68,129,288,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4013
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4014 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 134 41 280 33 108 172 300), lower := (rows 19 70 134 41 280 33 64 128 256), losses := [] }

theorem u4014 : Upper (D 5) (R 5) [18,68,130,33,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4014
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4015 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 272, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 70 134 41 280 36 105 169 297), lower := (rows 19 70 134 41 280 36 64 128 256), losses := [] }

theorem u4015 : Upper (D 5) (R 5) [18,68,130,33,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4015
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4016 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 134 41 280 40 101 165 293), lower := (rows 19 70 134 41 280 40 64 128 256), losses := [] }

theorem u4016 : Upper (D 5) (R 5) [18,68,130,33,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4016
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4017 : PairBound 9 := { available := 296, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 134 44 25 33 360 424 296), lower := (rows 19 70 134 44 25 33 64 128 256), losses := [] }

theorem u4017 : Upper (D 5) (R 5) [18,68,130,36,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4017
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4018 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 134 44 25 40 353 417 289), lower := (rows 19 70 134 44 25 40 64 128 256), losses := [] }

theorem u4018 : Upper (D 5) (R 5) [18,68,130,36,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4018
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4019 : Route 9 := (fun mask => (mask,id))

def c4019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4019 : Upper (D 5) (R 5) [18,68,130,36,9,256] 13 := by
  apply FastRouting.sound _ _ [18,68,130,36,9,256] 13 (by decide) (choices 1) [1,8,32] r4019 c4019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1334
  · exact u1335
  · exact u1336

#print axioms u4019
end Delivery.IrregularNine14.P05
