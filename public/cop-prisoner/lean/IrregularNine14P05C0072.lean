import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0025

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r4320 : Route 9 := (fun mask => (mask,id))

def c4320 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4320 : Upper (D 5) (R 5) [34,65,40,129,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,260,16] 13 (by decide) (choices 1) [2,4,8] r4320 c4320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1518
  · exact u1519
  · exact u1520

def b4321 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 137 280 34 84 148 276), lower := (rows 35 67 44 137 280 34 64 128 256), losses := [] }

theorem u4321 : Upper (D 5) (R 5) [34,65,40,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4321
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4322 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 137 280 36 86 150 278), lower := (rows 35 67 44 137 280 36 64 128 256), losses := [] }

theorem u4322 : Upper (D 5) (R 5) [34,65,40,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4322
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4323 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 35 67 44 137 280 48 70 134 262), lower := (rows 35 67 44 137 280 48 64 128 256), losses := [] }

theorem u4323 : Upper (D 5) (R 5) [34,65,40,129,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4323
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4324 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 138 273 36 92 156 284), lower := (rows 35 67 44 138 273 36 64 128 256), losses := [] }

theorem u4324 : Upper (D 5) (R 5) [34,65,40,130,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4324
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4325 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 44 138 273 40 84 148 276), lower := (rows 35 67 44 138 273 40 64 128 256), losses := [] }

theorem u4325 : Upper (D 5) (R 5) [34,65,40,130,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4325
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4326 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 140, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 138 273 48 76 140 268), lower := (rows 35 67 44 138 273 48 64 128 256), losses := [] }

theorem u4326 : Upper (D 5) (R 5) [34,65,40,130,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4326
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4327 : PairBound 9 := { available := 28, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 138 276 33 92 156 284), lower := (rows 35 67 44 138 276 33 64 128 256), losses := [] }

theorem u4327 : Upper (D 5) (R 5) [34,65,40,130,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4327
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4328 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 138 276 36 89 153 281), lower := (rows 35 67 44 138 276 36 64 128 256), losses := [] }

theorem u4328 : Upper (D 5) (R 5) [34,65,40,130,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4328
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4329 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 44 138 276 40 85 149 277), lower := (rows 35 67 44 138 276 40 64 128 256), losses := [] }

theorem u4329 : Upper (D 5) (R 5) [34,65,40,130,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4329
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4330 : Route 9 := (fun mask => (mask,id))

def c4330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4330 : Upper (D 5) (R 5) [34,65,40,130,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,260,16] 13 (by decide) (choices 1) [1,4,8] r4330 c4330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1521
  · exact u1522
  · exact u1523

def b4331 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 138 280 33 84 148 276), lower := (rows 35 67 44 138 280 33 64 128 256), losses := [] }

theorem u4331 : Upper (D 5) (R 5) [34,65,40,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4331
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4332 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 138 280 36 85 149 277), lower := (rows 35 67 44 138 280 36 64 128 256), losses := [] }

theorem u4332 : Upper (D 5) (R 5) [34,65,40,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4332
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4333 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 35 67 44 138 280 48 69 133 261), lower := (rows 35 67 44 138 280 48 64 128 256), losses := [] }

theorem u4333 : Upper (D 5) (R 5) [34,65,40,130,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4333
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4334 : PairBound 9 := { available := 280, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 140 22 33 344 408 280), lower := (rows 35 67 44 140 22 33 64 128 256), losses := [] }

theorem u4334 : Upper (D 5) (R 5) [34,65,40,132,6,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4334
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4335 : PairBound 9 := { available := 273, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 140 22 40 337 401 273), lower := (rows 35 67 44 140 22 40 64 128 256), losses := [] }

theorem u4335 : Upper (D 5) (R 5) [34,65,40,132,6,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4335
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4336 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 44 140 22 48 329 393 265), lower := (rows 35 67 44 140 22 48 64 128 256), losses := [] }

theorem u4336 : Upper (D 5) (R 5) [34,65,40,132,6,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4336
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4337 : Route 9 := (fun mask => (mask,id))

def c4337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4337 : Upper (D 5) (R 5) [34,65,40,132,6,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,6,256] 13 (by decide) (choices 1) [1,8,16] r4337 c4337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1524
  · exact u1525
  · exact u1526

def b4338 : PairBound 9 := { available := 276, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 140 26 33 340 404 276), lower := (rows 35 67 44 140 26 33 64 128 256), losses := [] }

theorem u4338 : Upper (D 5) (R 5) [34,65,40,132,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4338
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4339 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 44 140 26 48 325 389 261), lower := (rows 35 67 44 140 26 48 64 128 256), losses := [] }

theorem u4339 : Upper (D 5) (R 5) [34,65,40,132,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4339
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4340 : Route 9 := (fun mask => (mask,id))

def c4340 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4340 : Upper (D 5) (R 5) [34,65,40,132,10,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,10,256] 13 (by decide) (choices 1) [1,4,16] r4340 c4340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1527
  · exact u1528
  · exact u1529

def b4341 : PairBound 9 := { available := 28, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 140 273 34 92 156 284), lower := (rows 35 67 44 140 273 34 64 128 256), losses := [] }

theorem u4341 : Upper (D 5) (R 5) [34,65,40,132,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4341
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4342 : PairBound 9 := { available := 26, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 140 273 36 90 154 282), lower := (rows 35 67 44 140 273 36 64 128 256), losses := [] }

theorem u4342 : Upper (D 5) (R 5) [34,65,40,132,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4342
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4343 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 140 273 40 86 150 278), lower := (rows 35 67 44 140 273 40 64 128 256), losses := [] }

theorem u4343 : Upper (D 5) (R 5) [34,65,40,132,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4343
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4344 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 140, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 140 273 48 78 142 270), lower := (rows 35 67 44 140 273 48 64 128 256), losses := [] }

theorem u4344 : Upper (D 5) (R 5) [34,65,40,132,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4344
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4345 : PairBound 9 := { available := 28, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 140 274 33 92 156 284), lower := (rows 35 67 44 140 274 33 64 128 256), losses := [] }

theorem u4345 : Upper (D 5) (R 5) [34,65,40,132,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4345
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4346 : PairBound 9 := { available := 25, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 140 274 36 89 153 281), lower := (rows 35 67 44 140 274 36 64 128 256), losses := [] }

theorem u4346 : Upper (D 5) (R 5) [34,65,40,132,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4346
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4347 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 140 274 40 85 149 277), lower := (rows 35 67 44 140 274 40 64 128 256), losses := [] }

theorem u4347 : Upper (D 5) (R 5) [34,65,40,132,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4347
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4348 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 44 140 274 48 77 141 269), lower := (rows 35 67 44 140 274 48 64 128 256), losses := [] }

theorem u4348 : Upper (D 5) (R 5) [34,65,40,132,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4348
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4349 : PairBound 9 := { available := 268, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 152 22 33 332 396 268), lower := (rows 35 67 44 152 22 33 64 128 256), losses := [] }

theorem u4349 : Upper (D 5) (R 5) [34,65,40,144,6,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4349
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4350 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 323, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 44 152 22 36 329 393 265), lower := (rows 35 67 44 152 22 36 64 128 256), losses := [] }

theorem u4350 : Upper (D 5) (R 5) [34,65,40,144,6,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4350
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4351 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 323, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 44 152 22 40 325 389 261), lower := (rows 35 67 44 152 22 40 64 128 256), losses := [] }

theorem u4351 : Upper (D 5) (R 5) [34,65,40,144,6,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4351
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4352 : Route 9 := (fun mask => (mask,id))

def c4352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4352 : Upper (D 5) (R 5) [34,65,40,144,6,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,6,256] 13 (by decide) (choices 1) [1,4,8] r4352 c4352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1530
  · exact u1531
  · exact u1532

def b4353 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 152 273 34 76 140 268), lower := (rows 35 67 44 152 273 34 64 128 256), losses := [] }

theorem u4353 : Upper (D 5) (R 5) [34,65,40,144,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4353
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4354 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 152 273 36 78 142 270), lower := (rows 35 67 44 152 273 36 64 128 256), losses := [] }

theorem u4354 : Upper (D 5) (R 5) [34,65,40,144,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4354
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4355 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 44 152 273 40 70 134 262), lower := (rows 35 67 44 152 273 40 64 128 256), losses := [] }

theorem u4355 : Upper (D 5) (R 5) [34,65,40,144,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4355
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4356 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 152 274 33 76 140 268), lower := (rows 35 67 44 152 274 33 64 128 256), losses := [] }

theorem u4356 : Upper (D 5) (R 5) [34,65,40,144,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4356
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4357 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 152 274 36 77 141 269), lower := (rows 35 67 44 152 274 36 64 128 256), losses := [] }

theorem u4357 : Upper (D 5) (R 5) [34,65,40,144,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4357
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4358 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 44 152 274 40 69 133 261), lower := (rows 35 67 44 152 274 40 64 128 256), losses := [] }

theorem u4358 : Upper (D 5) (R 5) [34,65,40,144,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4358
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4359 : PairBound 9 := { available := 14, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 152 276 33 78 142 270), lower := (rows 35 67 44 152 276 33 64 128 256), losses := [] }

theorem u4359 : Upper (D 5) (R 5) [34,65,40,144,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4359
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4360 : PairBound 9 := { available := 13, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 152 276 34 77 141 269), lower := (rows 35 67 44 152 276 34 64 128 256), losses := [] }

theorem u4360 : Upper (D 5) (R 5) [34,65,40,144,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4360
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4361 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 67, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 44 152 276 36 75 139 267), lower := (rows 35 67 44 152 276 36 64 128 256), losses := [] }

theorem u4361 : Upper (D 5) (R 5) [34,65,40,144,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4361
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4362 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 44 152 276 40 71 135 263), lower := (rows 35 67 44 152 276 40 64 128 256), losses := [] }

theorem u4362 : Upper (D 5) (R 5) [34,65,40,144,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4362
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4363 : PairBound 9 := { available := 28, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 392 22 33 92 156 284), lower := (rows 35 67 44 392 22 33 64 128 256), losses := [] }

theorem u4363 : Upper (D 5) (R 5) [34,65,40,384,6,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4363
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4364 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 392 22 36 89 153 281), lower := (rows 35 67 44 392 22 36 64 128 256), losses := [] }

theorem u4364 : Upper (D 5) (R 5) [34,65,40,384,6,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4364
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4365 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 83, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 44 392 22 40 85 149 277), lower := (rows 35 67 44 392 22 40 64 128 256), losses := [] }

theorem u4365 : Upper (D 5) (R 5) [34,65,40,384,6,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4365
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4366 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 44 392 22 48 77 141 269), lower := (rows 35 67 44 392 22 48 64 128 256), losses := [] }

theorem u4366 : Upper (D 5) (R 5) [34,65,40,384,6,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4366
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4367 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 392 25 34 84 148 276), lower := (rows 35 67 44 392 25 34 64 128 256), losses := [] }

theorem u4367 : Upper (D 5) (R 5) [34,65,40,384,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4367
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4368 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 392 25 36 86 150 278), lower := (rows 35 67 44 392 25 36 64 128 256), losses := [] }

theorem u4368 : Upper (D 5) (R 5) [34,65,40,384,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4368
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4369 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 396, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 392 25 48 70 134 262), lower := (rows 35 67 44 392 25 48 64 128 256), losses := [] }

theorem u4369 : Upper (D 5) (R 5) [34,65,40,384,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4369
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4370 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 392 26 33 84 148 276), lower := (rows 35 67 44 392 26 33 64 128 256), losses := [] }

theorem u4370 : Upper (D 5) (R 5) [34,65,40,384,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4370
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4371 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 392 26 36 85 149 277), lower := (rows 35 67 44 392 26 36 64 128 256), losses := [] }

theorem u4371 : Upper (D 5) (R 5) [34,65,40,384,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4371
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4372 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 44 392 26 48 69 133 261), lower := (rows 35 67 44 392 26 48 64 128 256), losses := [] }

theorem u4372 : Upper (D 5) (R 5) [34,65,40,384,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4372
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4373 : PairBound 9 := { available := 268, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 137 28 34 332 396 268), lower := (rows 35 67 52 137 28 34 64 128 256), losses := [] }

theorem u4373 : Upper (D 5) (R 5) [34,65,48,129,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4373
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4374 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 67 52 137 28 36 330 394 266), lower := (rows 35 67 52 137 28 36 64 128 256), losses := [] }

theorem u4374 : Upper (D 5) (R 5) [34,65,48,129,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4374
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4375 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 137 28 40 326 390 262), lower := (rows 35 67 52 137 28 40 64 128 256), losses := [] }

theorem u4375 : Upper (D 5) (R 5) [34,65,48,129,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4375
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4376 : Route 9 := (fun mask => (mask,id))

def c4376 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4376 : Upper (D 5) (R 5) [34,65,48,129,12,256] 13 := by
  apply FastRouting.sound _ _ [34,65,48,129,12,256] 13 (by decide) (choices 1) [2,4,8] r4376 c4376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1533
  · exact u1534
  · exact u1535

def b4377 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 137 274 36 76 140 268), lower := (rows 35 67 52 137 274 36 64 128 256), losses := [] }

theorem u4377 : Upper (D 5) (R 5) [34,65,48,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4377
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4378 : PairBound 9 := { available := 12, camps := [], pairs := [(2,0),(4,0)], upper := (rows 35 67 52 137 274 40 76 140 268), lower := (rows 35 67 52 137 274 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 13 8 17 40 104 168 296), good := (rows 502 86 500 508 274 492 64 128 256) }] }

theorem u4378 : Upper (D 5) (R 5) [34,65,48,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4378
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4379 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 137 276 34 76 140 268), lower := (rows 35 67 52 137 276 34 64 128 256), losses := [] }

theorem u4379 : Upper (D 5) (R 5) [34,65,48,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4379
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u4379
end Delivery.IrregularNine14.P05
