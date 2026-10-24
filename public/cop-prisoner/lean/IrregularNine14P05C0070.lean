import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0024

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4200 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 44 137 280 34 69 133 261), lower := (rows 19 98 44 137 280 34 64 128 256), losses := [] }

theorem u4200 : Upper (D 5) (R 5) [18,96,40,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4200
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4201 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 98 44 137 280 36 71 135 263), lower := (rows 19 98 44 137 280 36 64 128 256), losses := [] }

theorem u4201 : Upper (D 5) (R 5) [18,96,40,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4201
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4202 : PairBound 9 := { available := 268, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 44 138 21 33 332 396 268), lower := (rows 19 98 44 138 21 33 64 128 256), losses := [] }

theorem u4202 : Upper (D 5) (R 5) [18,96,40,130,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4202
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4203 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 392, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 19 98 44 138 21 36 329 393 265), lower := (rows 19 98 44 138 21 36 64 128 256), losses := [] }

theorem u4203 : Upper (D 5) (R 5) [18,96,40,130,5,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4203
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4204 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 98 44 138 21 40 325 389 261), lower := (rows 19 98 44 138 21 40 64 128 256), losses := [] }

theorem u4204 : Upper (D 5) (R 5) [18,96,40,130,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4204
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4205 : PairBound 9 := { available := 13, camps := [], pairs := [(3,5)], upper := (rows 19 98 44 138 21 288 77 141 269), lower := (rows 19 98 44 138 21 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 16 0 80 144 272), good := (rows 475 66 12 138 477 256 64 128 256) }] }

theorem u4205 : Upper (D 5) (R 5) [18,96,40,130,5,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4205
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4206 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 44 138 273 33 76 140 268), lower := (rows 19 98 44 138 273 33 64 128 256), losses := [] }

theorem u4206 : Upper (D 5) (R 5) [18,96,40,130,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4206
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4207 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 98 44 138 273 36 77 141 269), lower := (rows 19 98 44 138 273 36 64 128 256), losses := [] }

theorem u4207 : Upper (D 5) (R 5) [18,96,40,130,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4207
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4208 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 98 44 138 273 40 69 133 261), lower := (rows 19 98 44 138 273 40 64 128 256), losses := [] }

theorem u4208 : Upper (D 5) (R 5) [18,96,40,130,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4208
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4209 : Route 9 := (fun mask => (mask,id))

def c4209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4209 : Upper (D 5) (R 5) [18,96,40,130,260,1] 13 := by
  apply FastRouting.sound _ _ [18,96,40,130,260,1] 13 (by decide) (choices 1) [1,4,8] r4209 c4209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1451
  · exact u1452
  · exact u1453

def b4210 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 19 98 44 138 276 36 73 137 265), lower := (rows 19 98 44 138 276 36 64 128 256), losses := [] }

theorem u4210 : Upper (D 5) (R 5) [18,96,40,130,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4210
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4211 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 98 44 138 276 40 69 133 261), lower := (rows 19 98 44 138 276 40 64 128 256), losses := [] }

theorem u4211 : Upper (D 5) (R 5) [18,96,40,130,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4211
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4212 : Route 9 := (fun mask => (mask,id))

def c4212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4212 : Upper (D 5) (R 5) [18,96,40,130,264,1] 13 := by
  apply FastRouting.sound _ _ [18,96,40,130,264,1] 13 (by decide) (choices 1) [1,4] r4212 c4212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1454
  · exact u1455

def b4213 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 98 44 138 280 36 69 133 261), lower := (rows 19 98 44 138 280 36 64 128 256), losses := [] }

theorem u4213 : Upper (D 5) (R 5) [18,96,40,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4213
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4214 : PairBound 9 := { available := 266, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 44 140 21 33 330 394 266), lower := (rows 19 98 44 140 21 33 64 128 256), losses := [] }

theorem u4214 : Upper (D 5) (R 5) [18,96,40,132,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4214
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4215 : PairBound 9 := { available := 265, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 44 140 21 34 329 393 265), lower := (rows 19 98 44 140 21 34 64 128 256), losses := [] }

theorem u4215 : Upper (D 5) (R 5) [18,96,40,132,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4215
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4216 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 98 44 140 21 40 323 387 259), lower := (rows 19 98 44 140 21 40 64 128 256), losses := [] }

theorem u4216 : Upper (D 5) (R 5) [18,96,40,132,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4216
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4217 : PairBound 9 := { available := 11, camps := [], pairs := [(3,5)], upper := (rows 19 98 44 140 21 288 75 139 267), lower := (rows 19 98 44 140 21 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 65 129 257), good := (rows 475 66 12 140 477 256 64 128 256) }] }

theorem u4217 : Upper (D 5) (R 5) [18,96,40,132,5,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4217
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4218 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 44 140 25 33 326 390 262), lower := (rows 19 98 44 140 25 33 64 128 256), losses := [] }

theorem u4218 : Upper (D 5) (R 5) [18,96,40,132,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4218
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4219 : PairBound 9 := { available := 261, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 44 140 25 34 325 389 261), lower := (rows 19 98 44 140 25 34 64 128 256), losses := [] }

theorem u4219 : Upper (D 5) (R 5) [18,96,40,132,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4219
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4220 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 98 44 140 25 36 323 387 259), lower := (rows 19 98 44 140 25 36 64 128 256), losses := [] }

theorem u4220 : Upper (D 5) (R 5) [18,96,40,132,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4220
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4221 : Route 9 := (fun mask => (mask,id))

def c4221 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4221 : Upper (D 5) (R 5) [18,96,40,132,9,256] 13 := by
  apply FastRouting.sound _ _ [18,96,40,132,9,256] 13 (by decide) (choices 1) [1,2,4] r4221 c4221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1456
  · exact u1457
  · exact u1458

def b4222 : PairBound 9 := { available := 14, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 44 140 273 33 78 142 270), lower := (rows 19 98 44 140 273 33 64 128 256), losses := [] }

theorem u4222 : Upper (D 5) (R 5) [18,96,40,132,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4222
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4223 : PairBound 9 := { available := 13, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 44 140 273 34 77 141 269), lower := (rows 19 98 44 140 273 34 64 128 256), losses := [] }

theorem u4223 : Upper (D 5) (R 5) [18,96,40,132,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4223
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4224 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 98 44 140 273 36 75 139 267), lower := (rows 19 98 44 140 273 36 64 128 256), losses := [] }

theorem u4224 : Upper (D 5) (R 5) [18,96,40,132,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4224
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4225 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 98 44 140 273 40 71 135 263), lower := (rows 19 98 44 140 273 40 64 128 256), losses := [] }

theorem u4225 : Upper (D 5) (R 5) [18,96,40,132,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4225
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4226 : Route 9 := (fun mask => (mask,id))

def c4226 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4226 : Upper (D 5) (R 5) [18,96,40,132,260,1] 13 := by
  apply FastRouting.sound _ _ [18,96,40,132,260,1] 13 (by decide) (choices 1) [1,2,8] r4226 c4226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1459
  · exact u1460
  · exact u1461

def b4227 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 44 140 276 34 73 137 265), lower := (rows 19 98 44 140 276 34 64 128 256), losses := [] }

theorem u4227 : Upper (D 5) (R 5) [18,96,40,132,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4227
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4228 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 98 44 140 276 40 67 131 259), lower := (rows 19 98 44 140 276 40 64 128 256), losses := [] }

theorem u4228 : Upper (D 5) (R 5) [18,96,40,132,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4228
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4229 : Route 9 := (fun mask => (mask,id))

def c4229 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4229 : Upper (D 5) (R 5) [18,96,40,132,264,1] 13 := by
  apply FastRouting.sound _ _ [18,96,40,132,264,1] 13 (by decide) (choices 1) [1,2,4] r4229 c4229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1462
  · exact u1463
  · exact u1464

def b4230 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 44 140 280 34 69 133 261), lower := (rows 19 98 44 140 280 34 64 128 256), losses := [] }

theorem u4230 : Upper (D 5) (R 5) [18,96,40,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4230
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4231 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 98 44 140 280 36 67 131 259), lower := (rows 19 98 44 140 280 36 64 128 256), losses := [] }

theorem u4231 : Upper (D 5) (R 5) [18,96,40,132,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4231
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4232 : PairBound 9 := { available := 14, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 44 392 21 33 78 142 270), lower := (rows 19 98 44 392 21 33 64 128 256), losses := [] }

theorem u4232 : Upper (D 5) (R 5) [18,96,40,384,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4232
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4233 : PairBound 9 := { available := 13, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 44 392 21 34 77 141 269), lower := (rows 19 98 44 392 21 34 64 128 256), losses := [] }

theorem u4233 : Upper (D 5) (R 5) [18,96,40,384,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4233
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4234 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 392, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 19 98 44 392 21 36 75 139 267), lower := (rows 19 98 44 392 21 36 64 128 256), losses := [] }

theorem u4234 : Upper (D 5) (R 5) [18,96,40,384,5,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4234
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4235 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 83, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 98 44 392 21 40 71 135 263), lower := (rows 19 98 44 392 21 40 64 128 256), losses := [] }

theorem u4235 : Upper (D 5) (R 5) [18,96,40,384,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4235
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4236 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 44 392 25 33 70 134 262), lower := (rows 19 98 44 392 25 33 64 128 256), losses := [] }

theorem u4236 : Upper (D 5) (R 5) [18,96,40,384,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4236
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4237 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 44 392 25 34 69 133 261), lower := (rows 19 98 44 392 25 34 64 128 256), losses := [] }

theorem u4237 : Upper (D 5) (R 5) [18,96,40,384,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4237
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4238 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 98 44 392 25 36 71 135 263), lower := (rows 19 98 44 392 25 36 64 128 256), losses := [] }

theorem u4238 : Upper (D 5) (R 5) [18,96,40,384,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4238
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4239 : PairBound 9 := { available := 44, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 133 265 28 34 108 172 300), lower := (rows 19 98 133 265 28 34 64 128 256), losses := [] }

theorem u4239 : Upper (D 5) (R 5) [18,96,129,257,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4239
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4240 : Route 9 := (fun mask => (mask,id))

def c4240 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4240 : Upper (D 5) (R 5) [18,96,129,257,12,4] 13 := by
  apply FastRouting.sound _ _ [18,96,129,257,12,4] 13 (by decide) (choices 1) [2,8,32] r4240 c4240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1465
  · exact u1466
  · exact u1467

def r4241 : Route 9 := (fun mask => (mask,id))

def c4241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4241 : Upper (D 5) (R 5) [18,96,129,258,12,1] 13 := by
  apply FastRouting.sound _ _ [18,96,129,258,12,1] 13 (by decide) (choices 1) [4,8,32] r4241 c4241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1468
  · exact u1469
  · exact u1470

def r4242 : Route 9 := (fun mask => (mask,id))

def c4242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4242 : Upper (D 5) (R 5) [18,96,129,258,12,4] 13 := by
  apply FastRouting.sound _ _ [18,96,129,258,12,4] 13 (by decide) (choices 1) [1,8,32] r4242 c4242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1471
  · exact u1472
  · exact u1473

def r4243 : Route 9 := (fun mask => (mask,id))

def c4243 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4243 : Upper (D 5) (R 5) [18,96,129,258,12,8] 13 := by
  apply FastRouting.sound _ _ [18,96,129,258,12,8] 13 (by decide) (choices 1) [1,4,32] r4243 c4243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1474
  · exact u1475
  · exact u1476

def r4244 : Route 9 := (fun mask => (mask,id))

def c4244 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4244 : Upper (D 5) (R 5) [18,96,129,288,12,1] 13 := by
  apply FastRouting.sound _ _ [18,96,129,288,12,1] 13 (by decide) (choices 1) [2,4,8] r4244 c4244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1477
  · exact u1478
  · exact u1479

def b4245 : PairBound 9 := { available := 13, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 133 296 28 34 77 141 269), lower := (rows 19 98 133 296 28 34 64 128 256), losses := [] }

theorem u4245 : Upper (D 5) (R 5) [18,96,129,288,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4245
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4246 : Route 9 := (fun mask => (mask,id))

def c4246 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4246 : Upper (D 5) (R 5) [18,96,129,288,12,4] 13 := by
  apply FastRouting.sound _ _ [18,96,129,288,12,4] 13 (by decide) (choices 1) [1,2,8] r4246 c4246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1480
  · exact u1481
  · exact u1482

def b4247 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 98 133 296 28 40 71 135 263), lower := (rows 19 98 133 296 28 40 64 128 256), losses := [] }

theorem u4247 : Upper (D 5) (R 5) [18,96,129,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4247
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4248 : PairBound 9 := { available := 44, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 134 268 25 33 108 172 300), lower := (rows 19 98 134 268 25 33 64 128 256), losses := [] }

theorem u4248 : Upper (D 5) (R 5) [18,96,130,260,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4248
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4249 : Route 9 := (fun mask => (mask,id))

def c4249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4249 : Upper (D 5) (R 5) [18,96,130,260,9,4] 13 := by
  apply FastRouting.sound _ _ [18,96,130,260,9,4] 13 (by decide) (choices 1) [1,8,32] r4249 c4249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1483
  · exact u1484
  · exact u1485

def r4250 : Route 9 := (fun mask => (mask,id))

def c4250 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4250 : Upper (D 5) (R 5) [18,96,130,260,9,8] 13 := by
  apply FastRouting.sound _ _ [18,96,130,260,9,8] 13 (by decide) (choices 1) [1,4,32] r4250 c4250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1486
  · exact u1487
  · exact u1488

def b4251 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 134 296 25 33 76 140 268), lower := (rows 19 98 134 296 25 33 64 128 256), losses := [] }

theorem u4251 : Upper (D 5) (R 5) [18,96,130,288,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4251
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4252 : Route 9 := (fun mask => (mask,id))

def c4252 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4252 : Upper (D 5) (R 5) [18,96,130,288,9,4] 13 := by
  apply FastRouting.sound _ _ [18,96,130,288,9,4] 13 (by decide) (choices 1) [1,4,8] r4252 c4252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1489
  · exact u1490
  · exact u1491

def b4253 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 98 134 296 25 40 69 133 261), lower := (rows 19 98 134 296 25 40 64 128 256), losses := [] }

theorem u4253 : Upper (D 5) (R 5) [18,96,130,288,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4253
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4254 : Route 9 := (fun mask => (mask,id))

def c4254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4254 : Upper (D 5) (R 5) [18,96,130,288,12,1] 13 := by
  apply FastRouting.sound _ _ [18,96,130,288,12,1] 13 (by decide) (choices 1) [1,4,8] r4254 c4254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1492
  · exact u1493
  · exact u1494

def r4255 : Route 9 := (fun mask => (mask,id))

def c4255 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4255 : Upper (D 5) (R 5) [18,96,130,288,12,4] 13 := by
  apply FastRouting.sound _ _ [18,96,130,288,12,4] 13 (by decide) (choices 1) [1,8] r4255 c4255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1495
  · exact u1496

def b4256 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 98 134 296 28 40 69 133 261), lower := (rows 19 98 134 296 28 40 64 128 256), losses := [] }

theorem u4256 : Upper (D 5) (R 5) [18,96,130,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4256
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4257 : PairBound 9 := { available := 42, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 140 268 21 33 106 170 298), lower := (rows 19 98 140 268 21 33 64 128 256), losses := [] }

theorem u4257 : Upper (D 5) (R 5) [18,96,136,260,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4257
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4258 : PairBound 9 := { available := 41, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 140 268 21 34 105 169 297), lower := (rows 19 98 140 268 21 34 64 128 256), losses := [] }

theorem u4258 : Upper (D 5) (R 5) [18,96,136,260,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4258
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4259 : PairBound 9 := { available := 35, camps := [], pairs := [(0,2),(1,2)], upper := (rows 19 98 140 268 21 40 99 163 291), lower := (rows 19 98 140 268 21 40 64 128 256), losses := [{ target := 2, region := (rows 17 18 0 8 16 44 80 144 272), good := (rows 467 98 168 296 499 40 64 128 256) }] }

theorem u4259 : Upper (D 5) (R 5) [18,96,136,260,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4259
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u4259
end Delivery.IrregularNine14.P05
