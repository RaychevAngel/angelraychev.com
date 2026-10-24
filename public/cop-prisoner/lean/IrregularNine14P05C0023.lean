import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0001

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1380 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 110, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 140 44 280 34 96 129 257), lower := (rows 19 70 140 44 280 34 96 128 256), losses := [] }

theorem u1380 : Upper (D 5) (R 5) [18,68,136,36,264,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1380
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1381 : PairBound 9 := { available := 10, camps := [], pairs := [(1,0),(2,0)], upper := (rows 19 70 140 44 304 33 65 138 266), lower := (rows 19 70 140 44 304 33 65 128 256), losses := [{ target := 0, region := (rows 0 66 37 56 48 32 64 129 257), good := (rows 414 70 140 60 316 444 454 128 256) }] }

theorem u1381 : Upper (D 5) (R 5) [18,68,136,36,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1381
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1382 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 172, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 140 44 304 33 66 137 265), lower := (rows 19 70 140 44 304 33 66 128 256), losses := [] }

theorem u1382 : Upper (D 5) (R 5) [18,68,136,36,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1382
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1383 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 44 304 33 72 131 259), lower := (rows 19 70 140 44 304 33 72 128 256), losses := [] }

theorem u1383 : Upper (D 5) (R 5) [18,68,136,36,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1383
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1384 : Route 9 := (fun mask => (mask,id))

def c1384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1384 : Upper (D 5) (R 5) [18,68,136,36,288,2,1] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,288,2,1] 13 (by decide) (choices 1) [1,8] r1384 c1384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u74
  · exact u75

def b1385 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 305, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 44 304 34 72 129 257), lower := (rows 19 70 140 44 304 34 72 128 256), losses := [] }

theorem u1385 : Upper (D 5) (R 5) [18,68,136,36,288,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1385
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1386 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 140 268 25 34 65 160 288), lower := (rows 19 70 140 268 25 34 65 128 256), losses := [] }

theorem u1386 : Upper (D 5) (R 5) [18,68,136,260,9,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1386
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1387 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 98, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 140 268 25 34 96 161 289), lower := (rows 19 70 140 268 25 34 96 128 256), losses := [] }

theorem u1387 : Upper (D 5) (R 5) [18,68,136,260,9,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1387
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1388 : Route 9 := (fun mask => (mask,id))

def c1388 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1388 : Upper (D 5) (R 5) [18,68,136,260,40,1,1] 13 := by
  apply FastRouting.sound _ _ [18,68,136,260,40,1,1] 13 (by decide) (choices 1) [2,32] r1388 c1388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u76
  · exact u77

def b1389 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 140 268 56 33 66 161 289), lower := (rows 19 70 140 268 56 33 66 128 256), losses := [] }

theorem u1389 : Upper (D 5) (R 5) [18,68,136,260,40,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1389
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1390 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 70 140 268 56 33 96 131 259), lower := (rows 19 70 140 268 56 33 96 128 256), losses := [] }

theorem u1390 : Upper (D 5) (R 5) [18,68,136,260,40,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1390
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1391 : Route 9 := (fun mask => (mask,id))

def c1391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1391 : Upper (D 5) (R 5) [18,68,136,260,40,2,1] 13 := by
  apply FastRouting.sound _ _ [18,68,136,260,40,2,1] 13 (by decide) (choices 1) [1,32] r1391 c1391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u78
  · exact u79

def b1392 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 396, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 19 70 140 268 56 34 96 129 257), lower := (rows 19 70 140 268 56 34 96 128 256), losses := [] }

theorem u1392 : Upper (D 5) (R 5) [18,68,136,260,40,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1392
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1393 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 140 296 25 34 65 164 292), lower := (rows 19 70 140 296 25 34 65 128 256), losses := [] }

theorem u1393 : Upper (D 5) (R 5) [18,68,136,288,9,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1393
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1394 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 70 140 296 25 34 68 161 289), lower := (rows 19 70 140 296 25 34 68 128 256), losses := [] }

theorem u1394 : Upper (D 5) (R 5) [18,68,136,288,9,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1394
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1395 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 98, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 140 296 25 34 96 133 261), lower := (rows 19 70 140 296 25 34 96 128 256), losses := [] }

theorem u1395 : Upper (D 5) (R 5) [18,68,136,288,9,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1395
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1396 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 83, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 140 296 25 36 65 162 290), lower := (rows 19 70 140 296 25 36 65 128 256), losses := [] }

theorem u1396 : Upper (D 5) (R 5) [18,68,136,288,9,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1396
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1397 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 140 296 25 36 66 161 289), lower := (rows 19 70 140 296 25 36 66 128 256), losses := [] }

theorem u1397 : Upper (D 5) (R 5) [18,68,136,288,9,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1397
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1398 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 98, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 140 296 25 36 96 131 259), lower := (rows 19 70 140 296 25 36 96 128 256), losses := [] }

theorem u1398 : Upper (D 5) (R 5) [18,68,136,288,9,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1398
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1399 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 164 42 276 33 65 136 264), lower := (rows 19 70 164 42 276 33 65 128 256), losses := [] }

theorem u1399 : Upper (D 5) (R 5) [18,68,160,34,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1399
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1400 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 74, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 164 42 276 33 72 137 265), lower := (rows 19 70 164 42 276 33 72 128 256), losses := [] }

theorem u1400 : Upper (D 5) (R 5) [18,68,160,34,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1400
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1401 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 164 42 280 33 65 140 268), lower := (rows 19 70 164 42 280 33 65 128 256), losses := [] }

theorem u1401 : Upper (D 5) (R 5) [18,68,160,34,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1401
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1402 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 70 164 42 280 33 68 137 265), lower := (rows 19 70 164 42 280 33 68 128 256), losses := [] }

theorem u1402 : Upper (D 5) (R 5) [18,68,160,34,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1402
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1403 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 164, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 70 164 42 280 33 72 133 261), lower := (rows 19 70 164 42 280 33 72 128 256), losses := [] }

theorem u1403 : Upper (D 5) (R 5) [18,68,160,34,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1403
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1404 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 164 265 28 33 66 168 296), lower := (rows 19 70 164 265 28 33 66 128 256), losses := [] }

theorem u1404 : Upper (D 5) (R 5) [18,68,160,257,12,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1404
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1405 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 164 265 28 33 72 162 290), lower := (rows 19 70 164 265 28 33 72 128 256), losses := [] }

theorem u1405 : Upper (D 5) (R 5) [18,68,160,257,12,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1405
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1406 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 281, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 70 164 265 28 33 96 138 266), lower := (rows 19 70 164 265 28 33 96 128 256), losses := [] }

theorem u1406 : Upper (D 5) (R 5) [18,68,160,257,12,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1406
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1407 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 70 164 265 28 34 65 168 296), lower := (rows 19 70 164 265 28 34 65 128 256), losses := [] }

theorem u1407 : Upper (D 5) (R 5) [18,68,160,257,12,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1407
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1408 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 164 265 28 34 72 161 289), lower := (rows 19 70 164 265 28 34 72 128 256), losses := [] }

theorem u1408 : Upper (D 5) (R 5) [18,68,160,257,12,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1408
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1409 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 102, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 164 265 28 34 96 137 265), lower := (rows 19 70 164 265 28 34 96 128 256), losses := [] }

theorem u1409 : Upper (D 5) (R 5) [18,68,160,257,12,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1409
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1410 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 164 265 28 40 65 162 290), lower := (rows 19 70 164 265 28 40 65 128 256), losses := [] }

theorem u1410 : Upper (D 5) (R 5) [18,68,160,257,12,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1410
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1411 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 164 265 28 40 66 161 289), lower := (rows 19 70 164 265 28 40 66 128 256), losses := [] }

theorem u1411 : Upper (D 5) (R 5) [18,68,160,257,12,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1411
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1412 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 70 164 265 28 40 96 131 259), lower := (rows 19 70 164 265 28 40 96 128 256), losses := [] }

theorem u1412 : Upper (D 5) (R 5) [18,68,160,257,12,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1412
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1413 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 70 164 266 28 33 65 168 296), lower := (rows 19 70 164 266 28 33 65 128 256), losses := [] }

theorem u1413 : Upper (D 5) (R 5) [18,68,160,258,12,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1413
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1414 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 164, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 70 164 266 28 33 72 161 289), lower := (rows 19 70 164 266 28 33 72 128 256), losses := [] }

theorem u1414 : Upper (D 5) (R 5) [18,68,160,258,12,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1414
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1415 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 281, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 70 164 266 28 33 96 137 265), lower := (rows 19 70 164 266 28 33 96 128 256), losses := [] }

theorem u1415 : Upper (D 5) (R 5) [18,68,160,258,12,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1415
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1416 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 164 268 25 34 65 168 296), lower := (rows 19 70 164 268 25 34 65 128 256), losses := [] }

theorem u1416 : Upper (D 5) (R 5) [18,68,160,260,9,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1416
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1417 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 164 268 25 34 72 161 289), lower := (rows 19 70 164 268 25 34 72 128 256), losses := [] }

theorem u1417 : Upper (D 5) (R 5) [18,68,160,260,9,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1417
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1418 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 102, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 164 268 25 34 96 137 265), lower := (rows 19 70 164 268 25 34 96 128 256), losses := [] }

theorem u1418 : Upper (D 5) (R 5) [18,68,160,260,9,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1418
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1419 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 164 268 25 40 65 162 290), lower := (rows 19 70 164 268 25 40 65 128 256), losses := [] }

theorem u1419 : Upper (D 5) (R 5) [18,68,160,260,9,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1419
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1420 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 164 268 25 40 66 161 289), lower := (rows 19 70 164 268 25 40 66 128 256), losses := [] }

theorem u1420 : Upper (D 5) (R 5) [18,68,160,260,9,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1420
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1421 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 70 164 268 25 40 96 131 259), lower := (rows 19 70 164 268 25 40 96 128 256), losses := [] }

theorem u1421 : Upper (D 5) (R 5) [18,68,160,260,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1421
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1422 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 83, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 70 164 268 49 40 65 138 266), lower := (rows 19 70 164 268 49 40 65 128 256), losses := [] }

theorem u1422 : Upper (D 5) (R 5) [18,68,160,260,33,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1422
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1423 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 164 268 49 40 66 137 265), lower := (rows 19 70 164 268 49 40 66 128 256), losses := [] }

theorem u1423 : Upper (D 5) (R 5) [18,68,160,260,33,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1423
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1424 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 66, targets := 1 },{ cop := 3, region := 66, targets := 32 }], pairs := [(1,0),(1,5)], upper := (rows 19 70 164 268 49 40 72 131 259), lower := (rows 19 70 164 268 49 40 72 128 256), losses := [] }

theorem u1424 : Upper (D 5) (R 5) [18,68,160,260,33,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1424
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1425 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 264, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 19 70 164 268 56 33 65 138 266), lower := (rows 19 70 164 268 56 33 65 128 256), losses := [] }

theorem u1425 : Upper (D 5) (R 5) [18,68,160,260,40,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1425
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1426 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 164 268 56 33 66 137 265), lower := (rows 19 70 164 268 56 33 66 128 256), losses := [] }

theorem u1426 : Upper (D 5) (R 5) [18,68,160,260,40,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1426
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1427 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 19 70 164 268 56 33 72 131 259), lower := (rows 19 70 164 268 56 33 72 128 256), losses := [] }

theorem u1427 : Upper (D 5) (R 5) [18,68,160,260,40,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1427
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1428 : Route 9 := (fun mask => (mask,id))

def c1428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1428 : Upper (D 5) (R 5) [18,68,160,260,40,2,1] 13 := by
  apply FastRouting.sound _ _ [18,68,160,260,40,2,1] 13 (by decide) (choices 1) [1,8] r1428 c1428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u80
  · exact u81

def b1429 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 114, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 19 70 164 268 56 34 72 129 257), lower := (rows 19 70 164 268 56 34 72 128 256), losses := [] }

theorem u1429 : Upper (D 5) (R 5) [18,68,160,260,40,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1429
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1430 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 164 296 25 34 65 140 268), lower := (rows 19 70 164 296 25 34 65 128 256), losses := [] }

theorem u1430 : Upper (D 5) (R 5) [18,68,160,288,9,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1430
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1431 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 102, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 164 296 25 34 68 137 265), lower := (rows 19 70 164 296 25 34 68 128 256), losses := [] }

theorem u1431 : Upper (D 5) (R 5) [18,68,160,288,9,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1431
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1432 : Route 9 := (fun mask => (mask,id))

def c1432 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1432 : Upper (D 5) (R 5) [18,68,160,288,9,2,8] 13 := by
  apply FastRouting.sound _ _ [18,68,160,288,9,2,8] 13 (by decide) (choices 1) [1,4] r1432 c1432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u82
  · exact u83

def b1433 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 388, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 388 42 28 33 65 168 296), lower := (rows 19 70 388 42 28 33 65 128 256), losses := [] }

theorem u1433 : Upper (D 5) (R 5) [18,68,384,34,12,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1433
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1434 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 420, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 70 388 42 28 33 72 161 289), lower := (rows 19 70 388 42 28 33 72 128 256), losses := [] }

theorem u1434 : Upper (D 5) (R 5) [18,68,384,34,12,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1434
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1435 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 19 70 388 42 28 33 96 137 265), lower := (rows 19 70 388 42 28 33 96 128 256), losses := [] }

theorem u1435 : Upper (D 5) (R 5) [18,68,384,34,12,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1435
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1436 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 388 44 25 34 65 168 296), lower := (rows 19 70 388 44 25 34 65 128 256), losses := [] }

theorem u1436 : Upper (D 5) (R 5) [18,68,384,36,9,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1436
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1437 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 388 44 25 34 72 161 289), lower := (rows 19 70 388 44 25 34 72 128 256), losses := [] }

theorem u1437 : Upper (D 5) (R 5) [18,68,384,36,9,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1437
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1438 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 106, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 388 44 25 34 96 137 265), lower := (rows 19 70 388 44 25 34 96 128 256), losses := [] }

theorem u1438 : Upper (D 5) (R 5) [18,68,384,36,9,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1438
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1439 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 172, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 98 37 137 276 40 66 140 268), lower := (rows 19 98 37 137 276 40 66 128 256), losses := [] }

theorem u1439 : Upper (D 5) (R 5) [18,96,33,129,260,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1439
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1439
end Delivery.IrregularNine14.P05
