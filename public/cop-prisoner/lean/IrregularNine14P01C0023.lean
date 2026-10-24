import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0003

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1380 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 275 38 69 56 144 40 194 194 450), lower := (rows 275 38 69 56 144 40 64 128 256), losses := [] }

theorem u1380 : Upper (D 1) (R 1) [274,36,65,48,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1380
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1381 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6)], upper := (rows 275 38 69 56 144 96 202 138 394), lower := (rows 275 38 69 56 144 96 64 128 256), losses := [] }

theorem u1381 : Upper (D 1) (R 1) [274,36,65,48,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1381
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1382 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 275 38 69 56 144 160 74 202 330), lower := (rows 275 38 69 56 144 160 64 128 256), losses := [] }

theorem u1382 : Upper (D 1) (R 1) [274,36,65,48,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1382
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1383 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 69 88 144 34 232 168 424), lower := (rows 275 38 69 88 144 34 64 128 256), losses := [] }

theorem u1383 : Upper (D 1) (R 1) [274,36,65,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1383
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1384 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 275 38 69 88 144 40 226 162 418), lower := (rows 275 38 69 88 144 40 64 128 256), losses := [] }

theorem u1384 : Upper (D 1) (R 1) [274,36,65,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1384
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1385 : Route 9 := (fun mask => (mask,id))

def c1385 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1385 : Upper (D 1) (R 1) [274,36,65,80,128,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,80,128,128] 13 (by decide) (choices 1) [2,8,32] r1385 c1385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u184
  · exact u185
  · exact u186

def b1386 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 69 104 144 34 216 152 408), lower := (rows 275 38 69 104 144 34 64 128 256), losses := [] }

theorem u1386 : Upper (D 1) (R 1) [274,36,65,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1386
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1387 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 275 38 69 104 144 40 210 146 402), lower := (rows 275 38 69 104 144 40 64 128 256), losses := [] }

theorem u1387 : Upper (D 1) (R 1) [274,36,65,96,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1387
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1388 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 69 104 144 48 202 138 394), lower := (rows 275 38 69 104 144 48 64 128 256), losses := [] }

theorem u1388 : Upper (D 1) (R 1) [274,36,65,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1388
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1389 : Route 9 := (fun mask => (mask,id))

def c1389 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1389 : Upper (D 1) (R 1) [274,36,65,96,128,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,96,128,128] 13 (by decide) (choices 1) [2,8,16] r1389 c1389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u187
  · exact u188
  · exact u189

def b1390 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 275 38 69 138 144 40 112 240 368), lower := (rows 275 38 69 138 144 40 64 128 256), losses := [] }

theorem u1390 : Upper (D 1) (R 1) [274,36,65,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1390
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1391 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 69 138 144 48 104 232 360), lower := (rows 275 38 69 138 144 48 64 128 256), losses := [] }

theorem u1391 : Upper (D 1) (R 1) [274,36,65,130,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1391
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1392 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6)], upper := (rows 275 38 69 138 144 96 120 184 312), lower := (rows 275 38 69 138 144 96 64 128 256), losses := [] }

theorem u1392 : Upper (D 1) (R 1) [274,36,65,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1392
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1393 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 69 168 144 34 88 216 344), lower := (rows 275 38 69 168 144 34 64 128 256), losses := [] }

theorem u1393 : Upper (D 1) (R 1) [274,36,65,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1393
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1394 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 275 38 69 168 144 40 82 210 338), lower := (rows 275 38 69 168 144 40 64 128 256), losses := [] }

theorem u1394 : Upper (D 1) (R 1) [274,36,65,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1394
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1395 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 275 38 69 168 144 48 74 202 330), lower := (rows 275 38 69 168 144 48 64 128 256), losses := [] }

theorem u1395 : Upper (D 1) (R 1) [274,36,65,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1395
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1396 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6)], upper := (rows 275 38 69 168 144 96 90 154 282), lower := (rows 275 38 69 168 144 96 64 128 256), losses := [] }

theorem u1396 : Upper (D 1) (R 1) [274,36,65,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1396
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1397 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 69 200 144 34 120 184 312), lower := (rows 275 38 69 200 144 34 64 128 256), losses := [] }

theorem u1397 : Upper (D 1) (R 1) [274,36,65,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1397
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1398 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 275 38 69 200 144 40 114 178 306), lower := (rows 275 38 69 200 144 40 64 128 256), losses := [] }

theorem u1398 : Upper (D 1) (R 1) [274,36,65,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1398
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1399 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 69 200 144 48 106 170 298), lower := (rows 275 38 69 200 144 48 64 128 256), losses := [] }

theorem u1399 : Upper (D 1) (R 1) [274,36,65,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1399
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1400 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 275 38 76 138 144 33 112 240 368), lower := (rows 275 38 76 138 144 33 64 128 256), losses := [] }

theorem u1400 : Upper (D 1) (R 1) [274,36,72,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1400
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1401 : PairBound 9 := { available := 97, camps := [], pairs := [(1,6)], upper := (rows 275 38 76 138 144 48 97 225 353), lower := (rows 275 38 76 138 144 48 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 152 189 0 128 256), good := (rows 307 38 62 186 176 48 0 176 256) }] }

theorem u1401 : Upper (D 1) (R 1) [274,36,72,130,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1401
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1402 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 275 38 76 138 144 96 113 177 305), lower := (rows 275 38 76 138 144 96 64 128 256), losses := [] }

theorem u1402 : Upper (D 1) (R 1) [274,36,72,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1402
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1403 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 275 98 13 138 144 36 112 240 368), lower := (rows 275 98 13 138 144 36 64 128 256), losses := [] }

theorem u1403 : Upper (D 1) (R 1) [274,96,9,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1403
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1404 : PairBound 9 := { available := 100, camps := [], pairs := [(1,7)], upper := (rows 275 98 13 138 144 48 100 228 356), lower := (rows 275 98 13 138 144 48 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 49 68 0 260), good := (rows 307 98 367 10 48 48 64 0 256) }] }

theorem u1404 : Upper (D 1) (R 1) [274,96,9,130,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1404
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1405 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 13 138 144 96 116 180 308), lower := (rows 275 98 13 138 144 96 64 128 256), losses := [] }

theorem u1405 : Upper (D 1) (R 1) [274,96,9,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1405
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1406 : PairBound 9 := { available := 84, camps := [{ cop := 6, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 13 168 144 34 84 212 340), lower := (rows 275 98 13 168 144 34 64 128 256), losses := [] }

theorem u1406 : Upper (D 1) (R 1) [274,96,9,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1406
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1407 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 275 98 13 168 144 36 82 210 338), lower := (rows 275 98 13 168 144 36 64 128 256), losses := [] }

theorem u1407 : Upper (D 1) (R 1) [274,96,9,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1407
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1408 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 275 98 13 168 144 48 70 198 326), lower := (rows 275 98 13 168 144 48 64 128 256), losses := [] }

theorem u1408 : Upper (D 1) (R 1) [274,96,9,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1408
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1409 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 13 168 144 96 86 150 278), lower := (rows 275 98 13 168 144 96 64 128 256), losses := [] }

theorem u1409 : Upper (D 1) (R 1) [274,96,9,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1409
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1410 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 275 98 14 137 144 36 112 240 368), lower := (rows 275 98 14 137 144 36 64 128 256), losses := [] }

theorem u1410 : Upper (D 1) (R 1) [274,96,10,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1410
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1411 : PairBound 9 := { available := 100, camps := [], pairs := [(1,7)], upper := (rows 275 98 14 137 144 48 100 228 356), lower := (rows 275 98 14 137 144 48 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 49 72 0 264), good := (rows 307 98 334 367 48 48 64 0 256) }] }

theorem u1411 : Upper (D 1) (R 1) [274,96,10,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1411
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1412 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 14 137 144 96 116 180 308), lower := (rows 275 98 14 137 144 96 64 128 256), losses := [] }

theorem u1412 : Upper (D 1) (R 1) [274,96,10,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1412
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1413 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 37 76 144 34 216 152 408), lower := (rows 275 98 37 76 144 34 64 128 256), losses := [] }

theorem u1413 : Upper (D 1) (R 1) [274,96,33,68,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1413
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1414 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 275 98 37 76 144 40 210 146 402), lower := (rows 275 98 37 76 144 40 64 128 256), losses := [] }

theorem u1414 : Upper (D 1) (R 1) [274,96,33,68,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1414
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1415 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 37 76 144 48 202 138 394), lower := (rows 275 98 37 76 144 48 64 128 256), losses := [] }

theorem u1415 : Upper (D 1) (R 1) [274,96,33,68,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1415
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1416 : PairBound 9 := { available := 26, camps := [], pairs := [(2,1)], upper := (rows 275 98 37 76 144 160 90 154 282), lower := (rows 275 98 37 76 144 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 176 176 64 128 256), good := (rows 309 112 53 76 176 176 64 176 256) }] }

theorem u1416 : Upper (D 1) (R 1) [274,96,33,68,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1416
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1417 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 37 88 144 34 204 140 396), lower := (rows 275 98 37 88 144 34 64 128 256), losses := [] }

theorem u1417 : Upper (D 1) (R 1) [274,96,33,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1417
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1418 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 275 98 37 88 144 36 202 138 394), lower := (rows 275 98 37 88 144 36 64 128 256), losses := [] }

theorem u1418 : Upper (D 1) (R 1) [274,96,33,80,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1418
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1419 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 275 98 37 88 144 40 198 134 390), lower := (rows 275 98 37 88 144 40 64 128 256), losses := [] }

theorem u1419 : Upper (D 1) (R 1) [274,96,33,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1419
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1420 : PairBound 9 := { available := 14, camps := [], pairs := [(2,1)], upper := (rows 275 98 37 88 144 160 78 142 270), lower := (rows 275 98 37 88 144 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 10 176 176 64 128 256), good := (rows 317 120 53 120 176 176 64 176 256) }] }

theorem u1420 : Upper (D 1) (R 1) [274,96,33,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1420
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1421 : PairBound 9 := { available := 88, camps := [], pairs := [], upper := (rows 275 98 37 138 144 36 88 216 344), lower := (rows 275 98 37 138 144 36 64 128 256), losses := [] }

theorem u1421 : Upper (D 1) (R 1) [274,96,33,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1421
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1422 : PairBound 9 := { available := 84, camps := [], pairs := [], upper := (rows 275 98 37 138 144 40 84 212 340), lower := (rows 275 98 37 138 144 40 64 128 256), losses := [] }

theorem u1422 : Upper (D 1) (R 1) [274,96,33,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1422
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1423 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 37 138 144 48 76 204 332), lower := (rows 275 98 37 138 144 48 64 128 256), losses := [] }

theorem u1423 : Upper (D 1) (R 1) [274,96,33,130,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1423
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1424 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 37 138 144 96 92 156 284), lower := (rows 275 98 37 138 144 96 64 128 256), losses := [] }

theorem u1424 : Upper (D 1) (R 1) [274,96,33,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1424
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1425 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 37 140 144 34 88 216 344), lower := (rows 275 98 37 140 144 34 64 128 256), losses := [] }

theorem u1425 : Upper (D 1) (R 1) [274,96,33,132,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1425
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1426 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 275 98 37 140 144 40 82 210 338), lower := (rows 275 98 37 140 144 40 64 128 256), losses := [] }

theorem u1426 : Upper (D 1) (R 1) [274,96,33,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1426
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1427 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 37 140 144 48 74 202 330), lower := (rows 275 98 37 140 144 48 64 128 256), losses := [] }

theorem u1427 : Upper (D 1) (R 1) [274,96,33,132,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1427
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1428 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 37 140 144 96 90 154 282), lower := (rows 275 98 37 140 144 96 64 128 256), losses := [] }

theorem u1428 : Upper (D 1) (R 1) [274,96,33,132,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1428
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1429 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 37 200 144 34 92 156 284), lower := (rows 275 98 37 200 144 34 64 128 256), losses := [] }

theorem u1429 : Upper (D 1) (R 1) [274,96,33,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1429
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1430 : PairBound 9 := { available := 26, camps := [], pairs := [], upper := (rows 275 98 37 200 144 36 90 154 282), lower := (rows 275 98 37 200 144 36 64 128 256), losses := [] }

theorem u1430 : Upper (D 1) (R 1) [274,96,33,192,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1430
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1431 : PairBound 9 := { available := 22, camps := [], pairs := [], upper := (rows 275 98 37 200 144 40 86 150 278), lower := (rows 275 98 37 200 144 40 64 128 256), losses := [] }

theorem u1431 : Upper (D 1) (R 1) [274,96,33,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1431
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1432 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 37 200 144 48 78 142 270), lower := (rows 275 98 37 200 144 48 64 128 256), losses := [] }

theorem u1432 : Upper (D 1) (R 1) [274,96,33,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1432
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1433 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 275 98 44 88 144 33 198 134 390), lower := (rows 275 98 44 88 144 33 64 128 256), losses := [] }

theorem u1433 : Upper (D 1) (R 1) [274,96,40,80,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1433
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1434 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 44 88 144 34 197 133 389), lower := (rows 275 98 44 88 144 34 64 128 256), losses := [] }

theorem u1434 : Upper (D 1) (R 1) [274,96,40,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1434
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1435 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 275 98 44 88 144 36 195 131 387), lower := (rows 275 98 44 88 144 36 64 128 256), losses := [] }

theorem u1435 : Upper (D 1) (R 1) [274,96,40,80,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1435
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1436 : PairBound 9 := { available := 7, camps := [], pairs := [(2,1)], upper := (rows 275 98 44 88 144 160 71 135 263), lower := (rows 275 98 44 88 144 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 15 10 176 176 64 128 256), good := (rows 317 124 60 124 176 176 64 176 256) }] }

theorem u1436 : Upper (D 1) (R 1) [274,96,40,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1436
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1437 : PairBound 9 := { available := 84, camps := [{ cop := 6, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 44 137 144 34 84 212 340), lower := (rows 275 98 44 137 144 34 64 128 256), losses := [] }

theorem u1437 : Upper (D 1) (R 1) [274,96,40,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1437
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1438 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 275 98 44 137 144 36 82 210 338), lower := (rows 275 98 44 137 144 36 64 128 256), losses := [] }

theorem u1438 : Upper (D 1) (R 1) [274,96,40,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1438
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1439 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 52, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 44 137 144 48 70 198 326), lower := (rows 275 98 44 137 144 48 64 128 256), losses := [] }

theorem u1439 : Upper (D 1) (R 1) [274,96,40,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1439
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1439
end Delivery.IrregularNine14.P01
