import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0022
import IrregularNine14P05C0023

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4020 : PairBound 9 := { available := 264, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 134 44 49 33 328 392 264), lower := (rows 19 70 134 44 49 33 64 128 256), losses := [] }

theorem u4020 : Upper (D 5) (R 5) [18,68,130,36,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4020
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4021 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 134 44 49 40 329 393 265), lower := (rows 19 70 134 44 49 40 64 128 256), losses := [] }

theorem u4021 : Upper (D 5) (R 5) [18,68,130,36,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4021
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4022 : Route 9 := (fun mask => (mask,id))

def c4022 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4022 : Upper (D 5) (R 5) [18,68,130,36,33,256] 13 := by
  apply FastRouting.sound _ _ [18,68,130,36,33,256] 13 (by decide) (choices 1) [1,8] r4022 c4022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1337
  · exact u1338

def b4023 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 134 44 273 33 104 168 296), lower := (rows 19 70 134 44 273 33 64 128 256), losses := [] }

theorem u4023 : Upper (D 5) (R 5) [18,68,130,36,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4023
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4024 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 134 44 273 40 105 169 297), lower := (rows 19 70 134 44 273 40 64 128 256), losses := [] }

theorem u4024 : Upper (D 5) (R 5) [18,68,130,36,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4024
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4025 : Route 9 := (fun mask => (mask,id))

def c4025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4025 : Upper (D 5) (R 5) [18,68,130,36,264,1] 13 := by
  apply FastRouting.sound _ _ [18,68,130,36,264,1] 13 (by decide) (choices 1) [1,8,32] r4025 c4025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1339
  · exact u1340
  · exact u1341

def b4026 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 134 44 280 40 97 161 289), lower := (rows 19 70 134 44 280 40 64 128 256), losses := [] }

theorem u4026 : Upper (D 5) (R 5) [18,68,130,36,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4026
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4027 : Route 9 := (fun mask => (mask,id))

def c4027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4027 : Upper (D 5) (R 5) [18,68,130,36,288,1] 13 := by
  apply FastRouting.sound _ _ [18,68,130,36,288,1] 13 (by decide) (choices 1) [1,8] r4027 c4027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1342
  · exact u1343

def b4028 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 134 44 304 40 73 137 265), lower := (rows 19 70 134 44 304 40 64 128 256), losses := [] }

theorem u4028 : Upper (D 5) (R 5) [18,68,130,36,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4028
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4029 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 70 134 265 56 33 108 172 300), lower := (rows 19 70 134 265 56 33 64 128 256), losses := [] }

theorem u4029 : Upper (D 5) (R 5) [18,68,130,257,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4029
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4030 : PairBound 9 := { available := 41, camps := [], pairs := [(3,1),(4,1)], upper := (rows 19 70 134 265 56 36 105 169 297), lower := (rows 19 70 134 265 56 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 38 65 129 257), good := (rows 505 100 164 473 56 36 64 128 256) }] }

theorem u4030 : Upper (D 5) (R 5) [18,68,130,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4030
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4031 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 134 265 56 40 101 165 293), lower := (rows 19 70 134 265 56 40 64 128 256), losses := [] }

theorem u4031 : Upper (D 5) (R 5) [18,68,130,257,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4031
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4032 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 134 268 25 33 104 168 296), lower := (rows 19 70 134 268 25 33 64 128 256), losses := [] }

theorem u4032 : Upper (D 5) (R 5) [18,68,130,260,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4032
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4033 : Route 9 := (fun mask => (mask,id))

def c4033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4033 : Upper (D 5) (R 5) [18,68,130,260,9,8] 13 := by
  apply FastRouting.sound _ _ [18,68,130,260,9,8] 13 (by decide) (choices 1) [1,32] r4033 c4033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1344
  · exact u1345

def b4034 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 134 268 49 33 104 168 296), lower := (rows 19 70 134 268 49 33 64 128 256), losses := [] }

theorem u4034 : Upper (D 5) (R 5) [18,68,130,260,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4034
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4035 : Route 9 := (fun mask => (mask,id))

def c4035 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4035 : Upper (D 5) (R 5) [18,68,130,260,33,8] 13 := by
  apply FastRouting.sound _ _ [18,68,130,260,33,8] 13 (by decide) (choices 1) [1,8,32] r4035 c4035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1346
  · exact u1347
  · exact u1348

def r4036 : Route 9 := (fun mask => (mask,id))

def c4036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4036 : Upper (D 5) (R 5) [18,68,130,260,40,1] 13 := by
  apply FastRouting.sound _ _ [18,68,130,260,40,1] 13 (by decide) (choices 1) [1,8,32] r4036 c4036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1349
  · exact u1350
  · exact u1351

def b4037 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 134 268 56 40 97 161 289), lower := (rows 19 70 134 268 56 40 64 128 256), losses := [] }

theorem u4037 : Upper (D 5) (R 5) [18,68,130,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4037
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4038 : PairBound 9 := { available := 44, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 134 296 25 33 108 172 300), lower := (rows 19 70 134 296 25 33 64 128 256), losses := [] }

theorem u4038 : Upper (D 5) (R 5) [18,68,130,288,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4038
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4039 : PairBound 9 := { available := 41, camps := [], pairs := [(3,1),(4,1)], upper := (rows 19 70 134 296 25 36 105 169 297), lower := (rows 19 70 134 296 25 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 38 65 129 257), good := (rows 505 100 164 296 473 36 64 128 256) }] }

theorem u4039 : Upper (D 5) (R 5) [18,68,130,288,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4039
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4040 : PairBound 9 := { available := 37, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 134 296 25 40 101 165 293), lower := (rows 19 70 134 296 25 40 64 128 256), losses := [] }

theorem u4040 : Upper (D 5) (R 5) [18,68,130,288,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4040
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4041 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 134 296 49 33 76 140 268), lower := (rows 19 70 134 296 49 33 64 128 256), losses := [] }

theorem u4041 : Upper (D 5) (R 5) [18,68,130,288,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4041
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4042 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 134 296 49 36 73 137 265), lower := (rows 19 70 134 296 49 36 64 128 256), losses := [] }

theorem u4042 : Upper (D 5) (R 5) [18,68,130,288,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4042
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4043 : PairBound 9 := { available := 13, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 134 296 49 40 77 141 269), lower := (rows 19 70 134 296 49 40 64 128 256), losses := [] }

theorem u4043 : Upper (D 5) (R 5) [18,68,130,288,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4043
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4044 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 140 41 276 33 106 170 298), lower := (rows 19 70 140 41 276 33 64 128 256), losses := [] }

theorem u4044 : Upper (D 5) (R 5) [18,68,136,33,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4044
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4045 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 19 70 140 41 276 34 105 169 297), lower := (rows 19 70 140 41 276 34 64 128 256), losses := [] }

theorem u4045 : Upper (D 5) (R 5) [18,68,136,33,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4045
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4046 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 40, targets := 2 },{ cop := 0, region := 40, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 140 41 276 40 99 163 291), lower := (rows 19 70 140 41 276 40 64 128 256), losses := [] }

theorem u4046 : Upper (D 5) (R 5) [18,68,136,33,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4046
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4047 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 140 41 280 33 102 166 294), lower := (rows 19 70 140 41 280 33 64 128 256), losses := [] }

theorem u4047 : Upper (D 5) (R 5) [18,68,136,33,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4047
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4048 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 19 70 140 41 280 34 101 165 293), lower := (rows 19 70 140 41 280 34 64 128 256), losses := [] }

theorem u4048 : Upper (D 5) (R 5) [18,68,136,33,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4048
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4049 : Route 9 := (fun mask => (mask,id))

def c4049 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4049 : Upper (D 5) (R 5) [18,68,136,33,264,4] 13 := by
  apply FastRouting.sound _ _ [18,68,136,33,264,4] 13 (by decide) (choices 1) [1,2,32] r4049 c4049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1352
  · exact u1353
  · exact u1354

def b4050 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 140 42 52 33 329 393 265), lower := (rows 19 70 140 42 52 33 64 128 256), losses := [] }

theorem u4050 : Upper (D 5) (R 5) [18,68,136,34,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4050
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4051 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 323, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 140 42 52 40 321 385 257), lower := (rows 19 70 140 42 52 40 64 128 256), losses := [] }

theorem u4051 : Upper (D 5) (R 5) [18,68,136,34,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4051
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4052 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(3,2)], upper := (rows 19 70 140 42 52 288 73 137 265), lower := (rows 19 70 140 42 52 288 64 128 256), losses := [] }

theorem u4052 : Upper (D 5) (R 5) [18,68,136,34,36,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4052
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4053 : PairBound 9 := { available := 44, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 140 42 273 33 108 172 300), lower := (rows 19 70 140 42 273 33 64 128 256), losses := [] }

theorem u4053 : Upper (D 5) (R 5) [18,68,136,34,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4053
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4054 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 273, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 140 42 273 36 105 169 297), lower := (rows 19 70 140 42 273 36 64 128 256), losses := [] }

theorem u4054 : Upper (D 5) (R 5) [18,68,136,34,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4054
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4055 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 70 140 42 273 40 101 165 293), lower := (rows 19 70 140 42 273 40 64 128 256), losses := [] }

theorem u4055 : Upper (D 5) (R 5) [18,68,136,34,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4055
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4056 : Route 9 := (fun mask => (mask,id))

def c4056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4056 : Upper (D 5) (R 5) [18,68,136,34,260,1] 13 := by
  apply FastRouting.sound _ _ [18,68,136,34,260,1] 13 (by decide) (choices 1) [1,8,32] r4056 c4056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1355
  · exact u1356
  · exact u1357

def b4057 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 70 140 42 276 40 97 161 289), lower := (rows 19 70 140 42 276 40 64 128 256), losses := [] }

theorem u4057 : Upper (D 5) (R 5) [18,68,136,34,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4057
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4058 : Route 9 := (fun mask => (mask,id))

def c4058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4058 : Upper (D 5) (R 5) [18,68,136,34,264,1] 13 := by
  apply FastRouting.sound _ _ [18,68,136,34,264,1] 13 (by decide) (choices 1) [1,4,32] r4058 c4058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1358
  · exact u1359
  · exact u1360

def b4059 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 273, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 140 42 280 36 97 161 289), lower := (rows 19 70 140 42 280 36 64 128 256), losses := [] }

theorem u4059 : Upper (D 5) (R 5) [18,68,136,34,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4059
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4060 : Route 9 := (fun mask => (mask,id))

def c4060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4060 : Upper (D 5) (R 5) [18,68,136,34,288,1] 13 := by
  apply FastRouting.sound _ _ [18,68,136,34,288,1] 13 (by decide) (choices 1) [1,4,8] r4060 c4060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1361
  · exact u1362
  · exact u1363

def b4061 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 273, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 140 42 304 36 73 137 265), lower := (rows 19 70 140 42 304 36 64 128 256), losses := [] }

theorem u4061 : Upper (D 5) (R 5) [18,68,136,34,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4061
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4062 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 70 140 42 304 40 69 133 261), lower := (rows 19 70 140 42 304 40 64 128 256), losses := [] }

theorem u4062 : Upper (D 5) (R 5) [18,68,136,34,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4062
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4063 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 140 44 25 33 354 418 290), lower := (rows 19 70 140 44 25 33 64 128 256), losses := [] }

theorem u4063 : Upper (D 5) (R 5) [18,68,136,36,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4063
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4064 : Route 9 := (fun mask => (mask,id))

def c4064 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4064 : Upper (D 5) (R 5) [18,68,136,36,9,2] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,9,2] 13 (by decide) (choices 1) [1,32,256] r4064 c4064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1364
  · exact u1365
  · exact u1366

def r4065 : Route 9 := (fun mask => (mask,id))

def c4065 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4065 : Upper (D 5) (R 5) [18,68,136,36,9,256] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,9,256] 13 (by decide) (choices 1) [1,2,32] r4065 c4065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1367
  · exact u1368
  · exact u1369

def b4066 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 44 49 33 330 394 266), lower := (rows 19 70 140 44 49 33 64 128 256), losses := [] }

theorem u4066 : Upper (D 5) (R 5) [18,68,136,36,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4066
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4067 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 44 49 34 329 393 265), lower := (rows 19 70 140 44 49 34 64 128 256), losses := [] }

theorem u4067 : Upper (D 5) (R 5) [18,68,136,36,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4067
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4068 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 140 44 49 40 323 387 259), lower := (rows 19 70 140 44 49 40 64 128 256), losses := [] }

theorem u4068 : Upper (D 5) (R 5) [18,68,136,36,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4068
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4069 : Route 9 := (fun mask => (mask,id))

def c4069 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4069 : Upper (D 5) (R 5) [18,68,136,36,33,256] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,33,256] 13 (by decide) (choices 1) [1,2,8] r4069 c4069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1370
  · exact u1371
  · exact u1372

def b4070 : PairBound 9 := { available := 42, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 140 44 273 33 106 170 298), lower := (rows 19 70 140 44 273 33 64 128 256), losses := [] }

theorem u4070 : Upper (D 5) (R 5) [18,68,136,36,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4070
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4071 : Route 9 := (fun mask => (mask,id))

def c4071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4071 : Upper (D 5) (R 5) [18,68,136,36,257,2] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,257,2] 13 (by decide) (choices 1) [1,8,32] r4071 c4071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1373
  · exact u1374
  · exact u1375

def b4072 : PairBound 9 := { available := 35, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 140 44 273 40 99 163 291), lower := (rows 19 70 140 44 273 40 64 128 256), losses := [] }

theorem u4072 : Upper (D 5) (R 5) [18,68,136,36,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4072
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4073 : Route 9 := (fun mask => (mask,id))

def c4073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4073 : Upper (D 5) (R 5) [18,68,136,36,264,1] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,264,1] 13 (by decide) (choices 1) [1,2,32] r4073 c4073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1376
  · exact u1377
  · exact u1378

def r4074 : Route 9 := (fun mask => (mask,id))

def c4074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4074 : Upper (D 5) (R 5) [18,68,136,36,264,2] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,264,2] 13 (by decide) (choices 1) [1,32] r4074 c4074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1379
  · exact u1380

def r4075 : Route 9 := (fun mask => (mask,id))

def c4075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4075 : Upper (D 5) (R 5) [18,68,136,36,288,1] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,288,1] 13 (by decide) (choices 1) [1,2,8] r4075 c4075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1381
  · exact u1382
  · exact u1383

def r4076 : Route 9 := (fun mask => (mask,id))

def c4076 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4076 : Upper (D 5) (R 5) [18,68,136,36,288,2] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,288,2] 13 (by decide) (choices 1) [1,8] r4076 c4076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1384
  · exact u1385

def b4077 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 140 44 304 40 67 131 259), lower := (rows 19 70 140 44 304 40 64 128 256), losses := [] }

theorem u4077 : Upper (D 5) (R 5) [18,68,136,36,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4077
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4078 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 140 265 52 33 106 170 298), lower := (rows 19 70 140 265 52 33 64 128 256), losses := [] }

theorem u4078 : Upper (D 5) (R 5) [18,68,136,257,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4078
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4079 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 140 265 52 34 105 169 297), lower := (rows 19 70 140 265 52 34 64 128 256), losses := [] }

theorem u4079 : Upper (D 5) (R 5) [18,68,136,257,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4079
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u4079
end Delivery.IrregularNine14.P05
