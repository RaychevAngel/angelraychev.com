import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0006

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1380 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 261 137 48 248 216 216 472), lower := (rows 51 70 261 137 48 32 64 128 256), losses := [] }

theorem u1380 : Upper (D 0) (R 0) [50,68,257,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1380
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1381 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 261 137 80 184 248 184 440), lower := (rows 51 70 261 137 80 32 64 128 256), losses := [] }

theorem u1381 : Upper (D 0) (R 0) [50,68,257,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1381
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1382_8 : Upper (D 0) (R 0) [50,68,257,129,128,8] 13 :=
  permutation_upper _ _ _ [50,68,257,129,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u371

theorem m1382_16 : Upper (D 0) (R 0) [50,68,257,129,128,16] 13 :=
  permutation_upper _ _ _ [50,68,257,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u372

theorem m1382_64 : Upper (D 0) (R 0) [50,68,257,129,128,64] 13 :=
  permutation_upper _ _ _ [50,68,257,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u373

def r1382 : Route 9 := (fun mask => (mask,id))

def c1382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1382 : Upper (D 0) (R 0) [50,68,257,129,128] 13 := by
  apply FastRouting.sound _ _ [50,68,257,129,128] 13 (by decide) (choices 1) [8,16,64] r1382 c1382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1382_8
  · exact m1382_16
  · exact m1382_64

def b1383 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 51 70 261 152 17 232 232 232 488), lower := (rows 51 70 261 152 17 32 64 128 256), losses := [] }

theorem u1383 : Upper (D 0) (R 0) [50,68,257,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1383
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1384 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 70 261 152 24 225 225 225 481), lower := (rows 51 70 261 152 24 32 64 128 256), losses := [] }

theorem u1384 : Upper (D 0) (R 0) [50,68,257,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1384
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1385 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 261 152 48 233 201 201 457), lower := (rows 51 70 261 152 48 32 64 128 256), losses := [] }

theorem u1385 : Upper (D 0) (R 0) [50,68,257,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1385
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1386 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 261 152 80 169 233 169 425), lower := (rows 51 70 261 152 80 32 64 128 256), losses := [] }

theorem u1386 : Upper (D 0) (R 0) [50,68,257,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1386
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1387 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 70 261 152 144 105 105 233 361), lower := (rows 51 70 261 152 144 32 64 128 256), losses := [] }

theorem u1387 : Upper (D 0) (R 0) [50,68,257,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1387
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1388 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 51 70 261 200 17 184 248 184 440), lower := (rows 51 70 261 200 17 32 64 128 256), losses := [] }

theorem u1388 : Upper (D 0) (R 0) [50,68,257,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1388
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1389 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 70 261 200 24 177 241 177 433), lower := (rows 51 70 261 200 24 32 64 128 256), losses := [] }

theorem u1389 : Upper (D 0) (R 0) [50,68,257,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1389
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1390 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 261 200 48 185 217 153 409), lower := (rows 51 70 261 200 48 32 64 128 256), losses := [] }

theorem u1390 : Upper (D 0) (R 0) [50,68,257,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1390
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1391_1 : Upper (D 0) (R 0) [50,68,257,192,128,1] 13 :=
  permutation_upper _ _ _ [50,68,257,192,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u374

theorem m1391_8 : Upper (D 0) (R 0) [50,68,257,192,128,8] 13 :=
  permutation_upper _ _ _ [50,68,257,192,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u375

theorem m1391_16 : Upper (D 0) (R 0) [50,68,257,192,128,16] 13 :=
  permutation_upper _ _ _ [50,68,257,192,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u376

def r1391 : Route 9 := (fun mask => (mask,id))

def c1391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1391 : Upper (D 0) (R 0) [50,68,257,192,128] 13 := by
  apply FastRouting.sound _ _ [50,68,257,192,128] 13 (by decide) (choices 1) [1,8,16] r1391 c1391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1391_1
  · exact m1391_8
  · exact m1391_16

def b1392 : PairBound 9 := { available := 240, camps := [], pairs := [(1,0)], upper := (rows 51 70 268 137 17 240 240 240 496), lower := (rows 51 70 268 137 17 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 49 81 145 273), good := (rows 498 70 270 494 496 32 64 128 256) }] }

theorem u1392 : Upper (D 0) (R 0) [50,68,264,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1392
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1393 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 268 137 48 241 209 209 465), lower := (rows 51 70 268 137 48 32 64 128 256), losses := [] }

theorem u1393 : Upper (D 0) (R 0) [50,68,264,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1393
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1394 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 268 137 80 177 241 177 433), lower := (rows 51 70 268 137 80 32 64 128 256), losses := [] }

theorem u1394 : Upper (D 0) (R 0) [50,68,264,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1394
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1395 : PairBound 9 := { available := 113, camps := [], pairs := [(1,7)], upper := (rows 51 70 268 137 144 113 113 241 369), lower := (rows 51 70 268 137 144 32 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 33 65 0 257), good := (rows 371 70 270 367 16 32 64 0 256) }] }

theorem u1395 : Upper (D 0) (R 0) [50,68,264,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1395
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1396 : PairBound 9 := { available := 225, camps := [], pairs := [(1,4)], upper := (rows 51 70 268 152 17 225 225 225 481), lower := (rows 51 70 268 152 17 32 64 128 256), losses := [{ target := 4, region := (rows 1 10 12 8 0 49 81 145 273), good := (rows 483 70 270 494 481 32 64 128 256) }] }

theorem u1396 : Upper (D 0) (R 0) [50,68,264,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1396
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1397 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 268 152 48 225 193 193 449), lower := (rows 51 70 268 152 48 32 64 128 256), losses := [] }

theorem u1397 : Upper (D 0) (R 0) [50,68,264,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1397
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1398 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 268 152 80 161 225 161 417), lower := (rows 51 70 268 152 80 32 64 128 256), losses := [] }

theorem u1398 : Upper (D 0) (R 0) [50,68,264,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1398
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1399 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 70 268 152 144 97 97 225 353), lower := (rows 51 70 268 152 144 32 64 128 256), losses := [] }

theorem u1399 : Upper (D 0) (R 0) [50,68,264,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1399
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1400 : Route 9 := (fun mask => (mask,id))

def c1400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1400 : Upper (D 0) (R 0) [50,68,384,80,1] 13 := by
  apply FastRouting.sound _ _ [50,68,384,80,1] 13 (by decide) (choices 1) [1,8,128] r1400 c1400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u377
  · exact u378
  · exact u379

def b1401 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 70 388 88 24 161 225 161 417), lower := (rows 51 70 388 88 24 32 64 128 256), losses := [] }

theorem u1401 : Upper (D 0) (R 0) [50,68,384,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1401
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1402 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 388 88 48 169 201 137 393), lower := (rows 51 70 388 88 48 32 64 128 256), losses := [] }

theorem u1402 : Upper (D 0) (R 0) [50,68,384,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1402
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1403 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 388 88 144 41 105 169 297), lower := (rows 51 70 388 88 144 32 64 128 256), losses := [] }

theorem u1403 : Upper (D 0) (R 0) [50,68,384,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1403
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1404 : Route 9 := (fun mask => (mask,id))

def c1404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1404 : Upper (D 0) (R 0) [50,68,384,129,1] 13 := by
  apply FastRouting.sound _ _ [50,68,384,129,1] 13 (by decide) (choices 1) [8,16,64] r1404 c1404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u380
  · exact u381
  · exact u382

def b1405 : PairBound 9 := { available := 113, camps := [], pairs := [], upper := (rows 51 70 388 137 24 113 113 241 369), lower := (rows 51 70 388 137 24 32 64 128 256), losses := [] }

theorem u1405 : Upper (D 0) (R 0) [50,68,384,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1405
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1406 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 388 137 48 121 89 217 345), lower := (rows 51 70 388 137 48 32 64 128 256), losses := [] }

theorem u1406 : Upper (D 0) (R 0) [50,68,384,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1406
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1407 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 388 137 80 57 121 185 313), lower := (rows 51 70 388 137 80 32 64 128 256), losses := [] }

theorem u1407 : Upper (D 0) (R 0) [50,68,384,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1407
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1408 : Route 9 := (fun mask => (mask,id))

def c1408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1408 : Upper (D 0) (R 0) [50,68,384,144,1] 13 := by
  apply FastRouting.sound _ _ [50,68,384,144,1] 13 (by decide) (choices 1) [1,8,64] r1408 c1408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u383
  · exact u384
  · exact u385

def b1409 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 51 70 388 152 24 97 97 225 353), lower := (rows 51 70 388 152 24 32 64 128 256), losses := [] }

theorem u1409 : Upper (D 0) (R 0) [50,68,384,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1409
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1410 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 388 152 48 105 73 201 329), lower := (rows 51 70 388 152 48 32 64 128 256), losses := [] }

theorem u1410 : Upper (D 0) (R 0) [50,68,384,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1410
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1411 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 388 152 80 41 105 169 297), lower := (rows 51 70 388 152 80 32 64 128 256), losses := [] }

theorem u1411 : Upper (D 0) (R 0) [50,68,384,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1411
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1412 : Route 9 := (fun mask => (mask,id))

def c1412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1412 : Upper (D 0) (R 0) [50,68,384,192,1] 13 := by
  apply FastRouting.sound _ _ [50,68,384,192,1] 13 (by decide) (choices 1) [1,8,16] r1412 c1412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u386
  · exact u387
  · exact u388

def b1413 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 51 70 388 200 24 49 113 177 305), lower := (rows 51 70 388 200 24 32 64 128 256), losses := [] }

theorem u1413 : Upper (D 0) (R 0) [50,68,384,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1413
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1414 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 388 200 48 57 89 153 281), lower := (rows 51 70 388 200 48 32 64 128 256), losses := [] }

theorem u1414 : Upper (D 0) (R 0) [50,68,384,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1414
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1415 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 51 194 13 268 17 240 240 240 496), lower := (rows 51 194 13 268 17 32 64 128 256), losses := [] }

theorem u1415 : Upper (D 0) (R 0) [50,192,9,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1415
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1416 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 13 268 48 241 209 209 465), lower := (rows 51 194 13 268 48 32 64 128 256), losses := [] }

theorem u1416 : Upper (D 0) (R 0) [50,192,9,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1416
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1417 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 13 268 80 177 241 177 433), lower := (rows 51 194 13 268 80 32 64 128 256), losses := [] }

theorem u1417 : Upper (D 0) (R 0) [50,192,9,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1417
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1418 : Route 9 := (fun mask => (mask,id))

def c1418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1418 : Upper (D 0) (R 0) [50,192,9,320,1] 13 := by
  apply FastRouting.sound _ _ [50,192,9,320,1] 13 (by decide) (choices 1) [4,16,128] r1418 c1418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u389
  · exact u390
  · exact u391

def b1419 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 194 13 328 20 177 241 177 433), lower := (rows 51 194 13 328 20 32 64 128 256), losses := [] }

theorem u1419 : Upper (D 0) (R 0) [50,192,9,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1419
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1420 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 13 328 48 181 213 149 405), lower := (rows 51 194 13 328 48 32 64 128 256), losses := [] }

theorem u1420 : Upper (D 0) (R 0) [50,192,9,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1420
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1421 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 13 328 144 53 117 181 309), lower := (rows 51 194 13 328 144 32 64 128 256), losses := [] }

theorem u1421 : Upper (D 0) (R 0) [50,192,9,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1421
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1422 : Route 9 := (fun mask => (mask,id))

def c1422 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1422 : Upper (D 0) (R 0) [50,192,24,96,1] 13 := by
  apply FastRouting.sound _ _ [50,192,24,96,1] 13 (by decide) (choices 1) [1,4,128,256] r1422 c1422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u392
  · exact u393
  · exact u394
  · exact u395

def b1423 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 51 194 28 104 20 417 449 385 385), lower := (rows 51 194 28 104 20 32 64 128 256), losses := [] }

theorem u1423 : Upper (D 0) (R 0) [50,192,24,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1423
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1424 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 28 104 144 293 325 389 261), lower := (rows 51 194 28 104 144 32 64 128 256), losses := [] }

theorem u1424 : Upper (D 0) (R 0) [50,192,24,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1424
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1425 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 51 194 28 104 272 165 197 133 389), lower := (rows 51 194 28 104 272 32 64 128 256), losses := [] }

theorem u1425 : Upper (D 0) (R 0) [50,192,24,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1425
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1426 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 28 265 17 228 228 228 484), lower := (rows 51 194 28 265 17 32 64 128 256), losses := [] }

theorem u1426 : Upper (D 0) (R 0) [50,192,24,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1426
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1427 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 194 28 265 20 225 225 225 481), lower := (rows 51 194 28 265 20 32 64 128 256), losses := [] }

theorem u1427 : Upper (D 0) (R 0) [50,192,24,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1427
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1428 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 28 265 48 229 197 197 453), lower := (rows 51 194 28 265 48 32 64 128 256), losses := [] }

theorem u1428 : Upper (D 0) (R 0) [50,192,24,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1428
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1429 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 28 265 80 165 229 165 421), lower := (rows 51 194 28 265 80 32 64 128 256), losses := [] }

theorem u1429 : Upper (D 0) (R 0) [50,192,24,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1429
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1430 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1430 : Upper (D 0) (R 0) [50,192,24,288,1] 13 := by
  apply FastRouting.sound _ _ [50,192,24,288,1] 13 (by decide) (choices 1) [1,4,64] r1430 c1430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u396
  · exact u397
  · exact u398

def b1431 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 51 194 28 296 20 225 193 193 449), lower := (rows 51 194 28 296 20 32 64 128 256), losses := [] }

theorem u1431 : Upper (D 0) (R 0) [50,192,24,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1431
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1432 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 28 296 80 165 197 133 389), lower := (rows 51 194 28 296 80 32 64 128 256), losses := [] }

theorem u1432 : Upper (D 0) (R 0) [50,192,24,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1432
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1433 : Route 9 := (fun mask => (mask,id))

def c1433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1433 : Upper (D 0) (R 0) [50,192,24,320,1] 13 := by
  apply FastRouting.sound _ _ [50,192,24,320,1] 13 (by decide) (choices 1) [1,4,128] r1433 c1433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u399
  · exact u400
  · exact u401

def b1434 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 194 28 328 20 161 225 161 417), lower := (rows 51 194 28 328 20 32 64 128 256), losses := [] }

theorem u1434 : Upper (D 0) (R 0) [50,192,24,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1434
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1435 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 28 328 48 165 197 133 389), lower := (rows 51 194 28 328 48 32 64 128 256), losses := [] }

theorem u1435 : Upper (D 0) (R 0) [50,192,24,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1435
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1436 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 28 328 144 37 101 165 293), lower := (rows 51 194 28 328 144 32 64 128 256), losses := [] }

theorem u1436 : Upper (D 0) (R 0) [50,192,24,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1436
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1437 : Route 9 := (fun mask => (mask,id))

def c1437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1437 : Upper (D 0) (R 0) [50,192,72,144,1] 13 := by
  apply FastRouting.sound _ _ [50,192,72,144,1] 13 (by decide) (choices 1) [1,4,256] r1437 c1437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u402
  · exact u403
  · exact u404

def b1438 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 51 194 76 152 20 289 353 417 289), lower := (rows 51 194 76 152 20 32 64 128 256), losses := [] }

theorem u1438 : Upper (D 0) (R 0) [50,192,72,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1438
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1439 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 76 152 48 293 325 389 261), lower := (rows 51 194 76 152 48 32 64 128 256), losses := [] }

theorem u1439 : Upper (D 0) (R 0) [50,192,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1439
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u1439
end Delivery.IrregularNine14.P00
