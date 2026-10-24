import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0023
import IrregularNine14P05C0024

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r4140 : Route 9 := (fun mask => (mask,id))

def c4140 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4140 : Upper (D 5) (R 5) [18,68,160,260,9,8] 13 := by
  apply FastRouting.sound _ _ [18,68,160,260,9,8] 13 (by decide) (choices 1) [1,2,32] r4140 c4140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1419
  · exact u1420
  · exact u1421

def b4141 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 164 268 49 33 74 138 266), lower := (rows 19 70 164 268 49 33 64 128 256), losses := [] }

theorem u4141 : Upper (D 5) (R 5) [18,68,160,260,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4141
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4142 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 164 268 49 34 73 137 265), lower := (rows 19 70 164 268 49 34 64 128 256), losses := [] }

theorem u4142 : Upper (D 5) (R 5) [18,68,160,260,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4142
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4143 : Route 9 := (fun mask => (mask,id))

def c4143 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4143 : Upper (D 5) (R 5) [18,68,160,260,33,8] 13 := by
  apply FastRouting.sound _ _ [18,68,160,260,33,8] 13 (by decide) (choices 1) [1,2,8] r4143 c4143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1422
  · exact u1423
  · exact u1424

def r4144 : Route 9 := (fun mask => (mask,id))

def c4144 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4144 : Upper (D 5) (R 5) [18,68,160,260,40,1] 13 := by
  apply FastRouting.sound _ _ [18,68,160,260,40,1] 13 (by decide) (choices 1) [1,2,8] r4144 c4144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1425
  · exact u1426
  · exact u1427

def r4145 : Route 9 := (fun mask => (mask,id))

def c4145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4145 : Upper (D 5) (R 5) [18,68,160,260,40,2] 13 := by
  apply FastRouting.sound _ _ [18,68,160,260,40,2] 13 (by decide) (choices 1) [1,8] r4145 c4145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1428
  · exact u1429

def b4146 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 164 268 56 40 67 131 259), lower := (rows 19 70 164 268 56 40 64 128 256), losses := [] }

theorem u4146 : Upper (D 5) (R 5) [18,68,160,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4146
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4147 : PairBound 9 := { available := 14, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 164 296 25 33 78 142 270), lower := (rows 19 70 164 296 25 33 64 128 256), losses := [] }

theorem u4147 : Upper (D 5) (R 5) [18,68,160,288,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4147
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4148 : Route 9 := (fun mask => (mask,id))

def c4148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4148 : Upper (D 5) (R 5) [18,68,160,288,9,2] 13 := by
  apply FastRouting.sound _ _ [18,68,160,288,9,2] 13 (by decide) (choices 1) [1,4,8] r4148 c4148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1430
  · exact u1431
  · exact u1432

def b4149 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 164 296 25 36 75 139 267), lower := (rows 19 70 164 296 25 36 64 128 256), losses := [] }

theorem u4149 : Upper (D 5) (R 5) [18,68,160,288,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4149
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4150 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 164 296 25 40 71 135 263), lower := (rows 19 70 164 296 25 40 64 128 256), losses := [] }

theorem u4150 : Upper (D 5) (R 5) [18,68,160,288,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4150
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4151 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 454, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 388 41 28 33 106 170 298), lower := (rows 19 70 388 41 28 33 64 128 256), losses := [] }

theorem u4151 : Upper (D 5) (R 5) [18,68,384,33,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4151
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4152 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 19 70 388 41 28 34 105 169 297), lower := (rows 19 70 388 41 28 34 64 128 256), losses := [] }

theorem u4152 : Upper (D 5) (R 5) [18,68,384,33,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4152
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4153 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 454, targets := 8 }], pairs := [(1,3),(2,3)], upper := (rows 19 70 388 41 28 40 99 163 291), lower := (rows 19 70 388 41 28 40 64 128 256), losses := [] }

theorem u4153 : Upper (D 5) (R 5) [18,68,384,33,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4153
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4154 : Route 9 := (fun mask => (mask,id))

def c4154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4154 : Upper (D 5) (R 5) [18,68,384,34,12,1] 13 := by
  apply FastRouting.sound _ _ [18,68,384,34,12,1] 13 (by decide) (choices 1) [1,8,32] r4154 c4154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1433
  · exact u1434
  · exact u1435

def b4155 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 70 388 42 28 40 97 161 289), lower := (rows 19 70 388 42 28 40 64 128 256), losses := [] }

theorem u4155 : Upper (D 5) (R 5) [18,68,384,34,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4155
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4156 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 388 42 52 33 73 137 265), lower := (rows 19 70 388 42 52 33 64 128 256), losses := [] }

theorem u4156 : Upper (D 5) (R 5) [18,68,384,34,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4156
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4157 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 70 388 42 52 40 73 137 265), lower := (rows 19 70 388 42 52 40 64 128 256), losses := [] }

theorem u4157 : Upper (D 5) (R 5) [18,68,384,34,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4157
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4158 : PairBound 9 := { available := 42, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 388 44 25 33 106 170 298), lower := (rows 19 70 388 44 25 33 64 128 256), losses := [] }

theorem u4158 : Upper (D 5) (R 5) [18,68,384,36,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4158
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4159 : Route 9 := (fun mask => (mask,id))

def c4159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4159 : Upper (D 5) (R 5) [18,68,384,36,9,2] 13 := by
  apply FastRouting.sound _ _ [18,68,384,36,9,2] 13 (by decide) (choices 1) [1,8,32] r4159 c4159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1436
  · exact u1437
  · exact u1438

def b4160 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 388 44 25 40 99 163 291), lower := (rows 19 70 388 44 25 40 64 128 256), losses := [] }

theorem u4160 : Upper (D 5) (R 5) [18,68,384,36,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4160
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4161 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 388 44 49 33 74 138 266), lower := (rows 19 70 388 44 49 33 64 128 256), losses := [] }

theorem u4161 : Upper (D 5) (R 5) [18,68,384,36,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4161
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4162 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 388 44 49 34 73 137 265), lower := (rows 19 70 388 44 49 34 64 128 256), losses := [] }

theorem u4162 : Upper (D 5) (R 5) [18,68,384,36,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4162
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4163 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 388 44 49 40 75 139 267), lower := (rows 19 70 388 44 49 40 64 128 256), losses := [] }

theorem u4163 : Upper (D 5) (R 5) [18,68,384,36,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4163
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4164 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 392, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 19 98 37 137 28 34 332 396 268), lower := (rows 19 98 37 137 28 34 64 128 256), losses := [] }

theorem u4164 : Upper (D 5) (R 5) [18,96,33,129,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4164
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4165 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 98 37 137 28 36 330 394 266), lower := (rows 19 98 37 137 28 36 64 128 256), losses := [] }

theorem u4165 : Upper (D 5) (R 5) [18,96,33,129,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4165
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4166 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 322, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 98 37 137 28 40 326 390 262), lower := (rows 19 98 37 137 28 40 64 128 256), losses := [] }

theorem u4166 : Upper (D 5) (R 5) [18,96,33,129,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4166
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4167 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 354, targets := 1 }], pairs := [(1,0)], upper := (rows 19 98 37 137 28 288 78 142 270), lower := (rows 19 98 37 137 28 288 64 128 256), losses := [] }

theorem u4167 : Upper (D 5) (R 5) [18,96,33,129,12,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4167
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4168 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 19 98 37 137 276 34 76 140 268), lower := (rows 19 98 37 137 276 34 64 128 256), losses := [] }

theorem u4168 : Upper (D 5) (R 5) [18,96,33,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4168
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4169 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 98 37 137 276 36 74 138 266), lower := (rows 19 98 37 137 276 36 64 128 256), losses := [] }

theorem u4169 : Upper (D 5) (R 5) [18,96,33,129,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4169
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4170 : Route 9 := (fun mask => (mask,id))

def c4170 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4170 : Upper (D 5) (R 5) [18,96,33,129,260,8] 13 := by
  apply FastRouting.sound _ _ [18,96,33,129,260,8] 13 (by decide) (choices 1) [2,4,8] r4170 c4170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1439
  · exact u1440
  · exact u1441

def b4171 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 19 98 37 137 280 34 76 140 268), lower := (rows 19 98 37 137 280 34 64 128 256), losses := [] }

theorem u4171 : Upper (D 5) (R 5) [18,96,33,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4171
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4172 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 98 37 137 280 36 78 142 270), lower := (rows 19 98 37 137 280 36 64 128 256), losses := [] }

theorem u4172 : Upper (D 5) (R 5) [18,96,33,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4172
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4173 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 66, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 98 37 137 280 40 70 134 262), lower := (rows 19 98 37 137 280 40 64 128 256), losses := [] }

theorem u4173 : Upper (D 5) (R 5) [18,96,33,129,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4173
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4174 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 98 37 138 28 33 332 396 268), lower := (rows 19 98 37 138 28 33 64 128 256), losses := [] }

theorem u4174 : Upper (D 5) (R 5) [18,96,33,130,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4174
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4175 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 98 37 138 28 36 329 393 265), lower := (rows 19 98 37 138 28 36 64 128 256), losses := [] }

theorem u4175 : Upper (D 5) (R 5) [18,96,33,130,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4175
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4176 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 322, targets := 8 }], pairs := [(1,3),(2,1)], upper := (rows 19 98 37 138 28 40 325 389 261), lower := (rows 19 98 37 138 28 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 56 69 133 261), good := (rows 501 96 485 168 508 40 64 128 256) }] }

theorem u4176 : Upper (D 5) (R 5) [18,96,33,130,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4176
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4177 : Route 9 := (fun mask => (mask,id))

def c4177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4177 : Upper (D 5) (R 5) [18,96,33,130,12,256] 13 := by
  apply FastRouting.sound _ _ [18,96,33,130,12,256] 13 (by decide) (choices 1) [1,4,8] r4177 c4177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1442
  · exact u1443
  · exact u1444

def b4178 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 98 37 138 276 33 76 140 268), lower := (rows 19 98 37 138 276 33 64 128 256), losses := [] }

theorem u4178 : Upper (D 5) (R 5) [18,96,33,130,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4178
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4179 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 98 37 138 276 36 73 137 265), lower := (rows 19 98 37 138 276 36 64 128 256), losses := [] }

theorem u4179 : Upper (D 5) (R 5) [18,96,33,130,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4179
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4180 : Route 9 := (fun mask => (mask,id))

def c4180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4180 : Upper (D 5) (R 5) [18,96,33,130,260,8] 13 := by
  apply FastRouting.sound _ _ [18,96,33,130,260,8] 13 (by decide) (choices 1) [1,4,8] r4180 c4180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1445
  · exact u1446
  · exact u1447

def b4181 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 98 37 138 280 33 76 140 268), lower := (rows 19 98 37 138 280 33 64 128 256), losses := [] }

theorem u4181 : Upper (D 5) (R 5) [18,96,33,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4181
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4182 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 98 37 138 280 36 77 141 269), lower := (rows 19 98 37 138 280 36 64 128 256), losses := [] }

theorem u4182 : Upper (D 5) (R 5) [18,96,33,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4182
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4183 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 66, targets := 8 }], pairs := [(1,3),(2,1)], upper := (rows 19 98 37 138 280 40 69 133 261), lower := (rows 19 98 37 138 280 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 56 69 133 261), good := (rows 501 96 485 168 312 40 64 128 256) }] }

theorem u4183 : Upper (D 5) (R 5) [18,96,33,130,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4183
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4184 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 98 37 140 276 33 74 138 266), lower := (rows 19 98 37 140 276 33 64 128 256), losses := [] }

theorem u4184 : Upper (D 5) (R 5) [18,96,33,132,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4184
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4185 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 19 98 37 140 276 34 73 137 265), lower := (rows 19 98 37 140 276 34 64 128 256), losses := [] }

theorem u4185 : Upper (D 5) (R 5) [18,96,33,132,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4185
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4186 : Route 9 := (fun mask => (mask,id))

def c4186 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4186 : Upper (D 5) (R 5) [18,96,33,132,260,8] 13 := by
  apply FastRouting.sound _ _ [18,96,33,132,260,8] 13 (by decide) (choices 1) [1,2,8] r4186 c4186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1448
  · exact u1449
  · exact u1450

def b4187 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 98 37 140 280 33 78 142 270), lower := (rows 19 98 37 140 280 33 64 128 256), losses := [] }

theorem u4187 : Upper (D 5) (R 5) [18,96,33,132,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4187
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4188 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 19 98 37 140 280 34 77 141 269), lower := (rows 19 98 37 140 280 34 64 128 256), losses := [] }

theorem u4188 : Upper (D 5) (R 5) [18,96,33,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4188
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4189 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 98 37 140 280 36 75 139 267), lower := (rows 19 98 37 140 280 36 64 128 256), losses := [] }

theorem u4189 : Upper (D 5) (R 5) [18,96,33,132,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4189
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4190 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 66, targets := 8 }], pairs := [(1,3),(2,1)], upper := (rows 19 98 37 140 280 40 71 135 263), lower := (rows 19 98 37 140 280 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 56 64 128 256), good := (rows 53 96 37 172 312 40 64 128 256) }] }

theorem u4190 : Upper (D 5) (R 5) [18,96,33,132,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4190
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4191 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 98 37 392 28 33 78 142 270), lower := (rows 19 98 37 392 28 33 64 128 256), losses := [] }

theorem u4191 : Upper (D 5) (R 5) [18,96,33,384,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4191
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4192 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 392, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 19 98 37 392 28 34 77 141 269), lower := (rows 19 98 37 392 28 34 64 128 256), losses := [] }

theorem u4192 : Upper (D 5) (R 5) [18,96,33,384,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4192
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4193 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 98 37 392 28 36 75 139 267), lower := (rows 19 98 37 392 28 36 64 128 256), losses := [] }

theorem u4193 : Upper (D 5) (R 5) [18,96,33,384,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4193
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4194 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 66, targets := 8 }], pairs := [(1,3),(2,1)], upper := (rows 19 98 37 392 28 40 71 135 263), lower := (rows 19 98 37 392 28 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 56 64 128 256), good := (rows 53 96 37 424 60 40 64 128 256) }] }

theorem u4194 : Upper (D 5) (R 5) [18,96,33,384,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4194
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4195 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 19 98 44 137 276 33 78 142 270), lower := (rows 19 98 44 137 276 33 64 128 256), losses := [] }

theorem u4195 : Upper (D 5) (R 5) [18,96,40,129,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4195
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4196 : PairBound 9 := { available := 13, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 44 137 276 34 77 141 269), lower := (rows 19 98 44 137 276 34 64 128 256), losses := [] }

theorem u4196 : Upper (D 5) (R 5) [18,96,40,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4196
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4197 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 19 98 44 137 276 36 75 139 267), lower := (rows 19 98 44 137 276 36 64 128 256), losses := [] }

theorem u4197 : Upper (D 5) (R 5) [18,96,40,129,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4197
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4198 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 98 44 137 276 40 71 135 263), lower := (rows 19 98 44 137 276 40 64 128 256), losses := [] }

theorem u4198 : Upper (D 5) (R 5) [18,96,40,129,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4198
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4199 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 19 98 44 137 280 33 70 134 262), lower := (rows 19 98 44 137 280 33 64 128 256), losses := [] }

theorem u4199 : Upper (D 5) (R 5) [18,96,40,129,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4199
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u4199
end Delivery.IrregularNine14.P05
