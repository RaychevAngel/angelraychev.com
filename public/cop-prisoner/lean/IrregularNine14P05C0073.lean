import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0025
import IrregularNine14P05C0026

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4380 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 137 276 36 74 138 266), lower := (rows 35 67 52 137 276 36 64 128 256), losses := [] }

theorem u4380 : Upper (D 5) (R 5) [34,65,48,129,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4380
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4381 : Route 9 := (fun mask => (mask,id))

def c4381 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4381 : Upper (D 5) (R 5) [34,65,48,129,260,8] 13 := by
  apply FastRouting.sound _ _ [34,65,48,129,260,8] 13 (by decide) (choices 1) [2,4,8] r4381 c4381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1536
  · exact u1537
  · exact u1538

def b4382 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 137 280 34 76 140 268), lower := (rows 35 67 52 137 280 34 64 128 256), losses := [] }

theorem u4382 : Upper (D 5) (R 5) [34,65,48,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4382
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4383 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 137 280 36 78 142 270), lower := (rows 35 67 52 137 280 36 64 128 256), losses := [] }

theorem u4383 : Upper (D 5) (R 5) [34,65,48,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4383
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4384 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 52 137 280 40 70 134 262), lower := (rows 35 67 52 137 280 40 64 128 256), losses := [] }

theorem u4384 : Upper (D 5) (R 5) [34,65,48,129,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4384
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4385 : PairBound 9 := { available := 268, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 138 28 33 332 396 268), lower := (rows 35 67 52 138 28 33 64 128 256), losses := [] }

theorem u4385 : Upper (D 5) (R 5) [34,65,48,130,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4385
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4386 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 67 52 138 28 36 329 393 265), lower := (rows 35 67 52 138 28 36 64 128 256), losses := [] }

theorem u4386 : Upper (D 5) (R 5) [34,65,48,130,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4386
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4387 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 138 28 40 325 389 261), lower := (rows 35 67 52 138 28 40 64 128 256), losses := [] }

theorem u4387 : Upper (D 5) (R 5) [34,65,48,130,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4387
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4388 : Route 9 := (fun mask => (mask,id))

def c4388 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4388 : Upper (D 5) (R 5) [34,65,48,130,12,256] 13 := by
  apply FastRouting.sound _ _ [34,65,48,130,12,256] 13 (by decide) (choices 1) [1,4,8] r4388 c4388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1539
  · exact u1540
  · exact u1541

def b4389 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 138 273 36 76 140 268), lower := (rows 35 67 52 138 273 36 64 128 256), losses := [] }

theorem u4389 : Upper (D 5) (R 5) [34,65,48,130,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4389
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4390 : Route 9 := (fun mask => (mask,id))

def c4390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4390 : Upper (D 5) (R 5) [34,65,48,130,257,8] 13 := by
  apply FastRouting.sound _ _ [34,65,48,130,257,8] 13 (by decide) (choices 1) [4,8] r4390 c4390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1542
  · exact u1543

def b4391 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 138 276 33 76 140 268), lower := (rows 35 67 52 138 276 33 64 128 256), losses := [] }

theorem u4391 : Upper (D 5) (R 5) [34,65,48,130,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4391
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4392 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 138 276 36 73 137 265), lower := (rows 35 67 52 138 276 36 64 128 256), losses := [] }

theorem u4392 : Upper (D 5) (R 5) [34,65,48,130,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4392
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4393 : Route 9 := (fun mask => (mask,id))

def c4393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4393 : Upper (D 5) (R 5) [34,65,48,130,260,8] 13 := by
  apply FastRouting.sound _ _ [34,65,48,130,260,8] 13 (by decide) (choices 1) [1,4,8] r4393 c4393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1544
  · exact u1545
  · exact u1546

def b4394 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 138 280 33 76 140 268), lower := (rows 35 67 52 138 280 33 64 128 256), losses := [] }

theorem u4394 : Upper (D 5) (R 5) [34,65,48,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4394
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4395 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 138 280 36 77 141 269), lower := (rows 35 67 52 138 280 36 64 128 256), losses := [] }

theorem u4395 : Upper (D 5) (R 5) [34,65,48,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4395
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4396 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 52 138 280 40 69 133 261), lower := (rows 35 67 52 138 280 40 64 128 256), losses := [] }

theorem u4396 : Upper (D 5) (R 5) [34,65,48,130,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4396
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4397 : PairBound 9 := { available := 268, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 140 25 34 332 396 268), lower := (rows 35 67 52 140 25 34 64 128 256), losses := [] }

theorem u4397 : Upper (D 5) (R 5) [34,65,48,132,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4397
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4398 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 140 25 36 330 394 266), lower := (rows 35 67 52 140 25 36 64 128 256), losses := [] }

theorem u4398 : Upper (D 5) (R 5) [34,65,48,132,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4398
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4399 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 323, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 52 140 25 40 326 390 262), lower := (rows 35 67 52 140 25 40 64 128 256), losses := [] }

theorem u4399 : Upper (D 5) (R 5) [34,65,48,132,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4399
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4400 : Route 9 := (fun mask => (mask,id))

def c4400 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4400 : Upper (D 5) (R 5) [34,65,48,132,9,256] 13 := by
  apply FastRouting.sound _ _ [34,65,48,132,9,256] 13 (by decide) (choices 1) [2,4,8] r4400 c4400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1547
  · exact u1548
  · exact u1549

def b4401 : PairBound 9 := { available := 268, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 140 26 33 332 396 268), lower := (rows 35 67 52 140 26 33 64 128 256), losses := [] }

theorem u4401 : Upper (D 5) (R 5) [34,65,48,132,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4401
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4402 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 140 26 36 329 393 265), lower := (rows 35 67 52 140 26 36 64 128 256), losses := [] }

theorem u4402 : Upper (D 5) (R 5) [34,65,48,132,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4402
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4403 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 323, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 52 140 26 40 325 389 261), lower := (rows 35 67 52 140 26 40 64 128 256), losses := [] }

theorem u4403 : Upper (D 5) (R 5) [34,65,48,132,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4403
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4404 : Route 9 := (fun mask => (mask,id))

def c4404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4404 : Upper (D 5) (R 5) [34,65,48,132,10,256] 13 := by
  apply FastRouting.sound _ _ [34,65,48,132,10,256] 13 (by decide) (choices 1) [1,4,8] r4404 c4404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1550
  · exact u1551
  · exact u1552

def b4405 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 140 273 34 76 140 268), lower := (rows 35 67 52 140 273 34 64 128 256), losses := [] }

theorem u4405 : Upper (D 5) (R 5) [34,65,48,132,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4405
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4406 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 140 273 36 74 138 266), lower := (rows 35 67 52 140 273 36 64 128 256), losses := [] }

theorem u4406 : Upper (D 5) (R 5) [34,65,48,132,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4406
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4407 : Route 9 := (fun mask => (mask,id))

def c4407 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4407 : Upper (D 5) (R 5) [34,65,48,132,257,8] 13 := by
  apply FastRouting.sound _ _ [34,65,48,132,257,8] 13 (by decide) (choices 1) [2,4,8] r4407 c4407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1553
  · exact u1554
  · exact u1555

def b4408 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 140 274 33 76 140 268), lower := (rows 35 67 52 140 274 33 64 128 256), losses := [] }

theorem u4408 : Upper (D 5) (R 5) [34,65,48,132,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4408
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4409 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 140 274 36 73 137 265), lower := (rows 35 67 52 140 274 36 64 128 256), losses := [] }

theorem u4409 : Upper (D 5) (R 5) [34,65,48,132,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4409
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4410 : Route 9 := (fun mask => (mask,id))

def c4410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4410 : Upper (D 5) (R 5) [34,65,48,132,258,8] 13 := by
  apply FastRouting.sound _ _ [34,65,48,132,258,8] 13 (by decide) (choices 1) [1,4,8] r4410 c4410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1556
  · exact u1557
  · exact u1558

def b4411 : PairBound 9 := { available := 14, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 140 280 33 78 142 270), lower := (rows 35 67 52 140 280 33 64 128 256), losses := [] }

theorem u4411 : Upper (D 5) (R 5) [34,65,48,132,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4411
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4412 : PairBound 9 := { available := 13, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 140 280 34 77 141 269), lower := (rows 35 67 52 140 280 34 64 128 256), losses := [] }

theorem u4412 : Upper (D 5) (R 5) [34,65,48,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4412
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4413 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 140 280 36 75 139 267), lower := (rows 35 67 52 140 280 36 64 128 256), losses := [] }

theorem u4413 : Upper (D 5) (R 5) [34,65,48,132,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4413
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4414 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 52 140 280 40 71 135 263), lower := (rows 35 67 52 140 280 40 64 128 256), losses := [] }

theorem u4414 : Upper (D 5) (R 5) [34,65,48,132,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4414
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4415 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 392 25 34 76 140 268), lower := (rows 35 67 52 392 25 34 64 128 256), losses := [] }

theorem u4415 : Upper (D 5) (R 5) [34,65,48,384,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4415
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4416 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 392 25 36 78 142 270), lower := (rows 35 67 52 392 25 36 64 128 256), losses := [] }

theorem u4416 : Upper (D 5) (R 5) [34,65,48,384,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4416
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4417 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 52 392 25 40 70 134 262), lower := (rows 35 67 52 392 25 40 64 128 256), losses := [] }

theorem u4417 : Upper (D 5) (R 5) [34,65,48,384,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4417
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4418 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 392 26 33 76 140 268), lower := (rows 35 67 52 392 26 33 64 128 256), losses := [] }

theorem u4418 : Upper (D 5) (R 5) [34,65,48,384,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4418
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4419 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 392 26 36 77 141 269), lower := (rows 35 67 52 392 26 36 64 128 256), losses := [] }

theorem u4419 : Upper (D 5) (R 5) [34,65,48,384,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4419
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4420 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 52 392 26 40 69 133 261), lower := (rows 35 67 52 392 26 40 64 128 256), losses := [] }

theorem u4420 : Upper (D 5) (R 5) [34,65,48,384,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4420
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4421 : PairBound 9 := { available := 14, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 392 28 33 78 142 270), lower := (rows 35 67 52 392 28 33 64 128 256), losses := [] }

theorem u4421 : Upper (D 5) (R 5) [34,65,48,384,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4421
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4422 : PairBound 9 := { available := 13, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 52 392 28 34 77 141 269), lower := (rows 35 67 52 392 28 34 64 128 256), losses := [] }

theorem u4422 : Upper (D 5) (R 5) [34,65,48,384,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4422
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4423 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 67 52 392 28 36 75 139 267), lower := (rows 35 67 52 392 28 36 64 128 256), losses := [] }

theorem u4423 : Upper (D 5) (R 5) [34,65,48,384,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4423
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4424 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 392 28 40 71 135 263), lower := (rows 35 67 52 392 28 40 64 128 256), losses := [] }

theorem u4424 : Upper (D 5) (R 5) [34,65,48,384,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4424
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4425 : Route 9 := (fun mask => (mask,id))

def c4425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4425 : Upper (D 5) (R 5) [34,65,129,258,12,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,258,12,4] 13 (by decide) (choices 1) [8,16,32] r4425 c4425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1559
  · exact u1560
  · exact u1561

def r4426 : Route 9 := (fun mask => (mask,id))

def c4426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4426 : Upper (D 5) (R 5) [34,65,129,258,12,8] 13 := by
  apply FastRouting.sound _ _ [34,65,129,258,12,8] 13 (by decide) (choices 1) [4,16,32] r4426 c4426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1562
  · exact u1563
  · exact u1564

def r4427 : Route 9 := (fun mask => (mask,id))

def c4427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4427 : Upper (D 5) (R 5) [34,65,129,258,12,16] 13 := by
  apply FastRouting.sound _ _ [34,65,129,258,12,16] 13 (by decide) (choices 1) [4,8,32] r4427 c4427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1565
  · exact u1566
  · exact u1567

def b4428 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 266 52 36 88 152 280), lower := (rows 35 67 133 266 52 36 64 128 256), losses := [] }

theorem u4428 : Upper (D 5) (R 5) [34,65,129,258,36,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4428
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4429 : Route 9 := (fun mask => (mask,id))

def c4429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4429 : Upper (D 5) (R 5) [34,65,129,258,36,8] 13 := by
  apply FastRouting.sound _ _ [34,65,129,258,36,8] 13 (by decide) (choices 1) [4,8,16] r4429 c4429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1568
  · exact u1569
  · exact u1570

def b4430 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 133 266 52 48 76 140 268), lower := (rows 35 67 133 266 52 48 64 128 256), losses := [] }

theorem u4430 : Upper (D 5) (R 5) [34,65,129,258,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4430
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4431 : Route 9 := (fun mask => (mask,id))

def c4431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4431 : Upper (D 5) (R 5) [34,65,129,258,40,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,258,40,4] 13 (by decide) (choices 1) [4,8,16] r4431 c4431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1571
  · exact u1572
  · exact u1573

def b4432 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 133 266 56 40 84 148 276), lower := (rows 35 67 133 266 56 40 64 128 256), losses := [] }

theorem u4432 : Upper (D 5) (R 5) [34,65,129,258,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4432
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4433 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 133 266 56 48 76 140 268), lower := (rows 35 67 133 266 56 48 64 128 256), losses := [] }

theorem u4433 : Upper (D 5) (R 5) [34,65,129,258,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4433
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4434 : PairBound 9 := { available := 56, camps := [], pairs := [(3,0),(4,0)], upper := (rows 35 67 133 268 26 36 120 184 312), lower := (rows 35 67 133 268 26 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 44 17 44 85 149 277), good := (rows 506 466 508 492 506 492 64 128 256) }] }

theorem u4434 : Upper (D 5) (R 5) [34,65,129,260,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4434
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4435 : Route 9 := (fun mask => (mask,id))

def c4435 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4435 : Upper (D 5) (R 5) [34,65,129,260,10,8] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260,10,8] 13 (by decide) (choices 1) [4,16,32] r4435 c4435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1574
  · exact u1575
  · exact u1576

def b4436 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 133 268 26 48 108 172 300), lower := (rows 35 67 133 268 26 48 64 128 256), losses := [] }

theorem u4436 : Upper (D 5) (R 5) [34,65,129,260,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4436
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4437 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 133 268 52 34 88 152 280), lower := (rows 35 67 133 268 52 34 64 128 256), losses := [] }

theorem u4437 : Upper (D 5) (R 5) [34,65,129,260,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4437
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4438 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 268 52 40 90 154 282), lower := (rows 35 67 133 268 52 40 64 128 256), losses := [] }

theorem u4438 : Upper (D 5) (R 5) [34,65,129,260,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4438
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4439 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 133 268 52 48 74 138 266), lower := (rows 35 67 133 268 52 48 64 128 256), losses := [] }

theorem u4439 : Upper (D 5) (R 5) [34,65,129,260,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4439
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u4439
end Delivery.IrregularNine14.P05
