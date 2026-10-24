import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0001

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1380 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 7 42 196 265 82 36 65 176 304), lower := (rows 7 42 196 265 82 36 65 128 256), losses := [] }

theorem u1380 : Upper (D 6) (R 6) [6,40,192,257,66,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1380
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1381 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 196 265 82 36 80 161 289), lower := (rows 7 42 196 265 82 36 80 128 256), losses := [] }

theorem u1381 : Upper (D 6) (R 6) [6,40,192,257,66,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1381
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1382 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 196 265 82 36 96 145 273), lower := (rows 7 42 196 265 82 36 96 128 256), losses := [] }

theorem u1382 : Upper (D 6) (R 6) [6,40,192,257,66,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1382
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1383 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 114, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 42 196 265 82 48 65 164 292), lower := (rows 7 42 196 265 82 48 65 128 256), losses := [] }

theorem u1383 : Upper (D 6) (R 6) [6,40,192,257,66,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1383
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1384 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 42 196 265 82 48 68 161 289), lower := (rows 7 42 196 265 82 48 68 128 256), losses := [] }

theorem u1384 : Upper (D 6) (R 6) [6,40,192,257,66,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1384
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1385 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 114, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 265 82 48 96 133 261), lower := (rows 7 42 196 265 82 48 96 128 256), losses := [] }

theorem u1385 : Upper (D 6) (R 6) [6,40,192,257,66,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1385
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1386 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 298, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 42 196 266 81 33 68 176 304), lower := (rows 7 42 196 266 81 33 68 128 256), losses := [] }

theorem u1386 : Upper (D 6) (R 6) [6,40,192,258,65,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1386
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1387 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 299, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 196 266 81 33 80 164 292), lower := (rows 7 42 196 266 81 33 80 128 256), losses := [] }

theorem u1387 : Upper (D 6) (R 6) [6,40,192,258,65,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1387
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1388 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 132, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 42 196 266 81 33 96 148 276), lower := (rows 7 42 196 266 81 33 96 128 256), losses := [] }

theorem u1388 : Upper (D 6) (R 6) [6,40,192,258,65,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1388
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1389 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 42 196 266 112 33 65 148 276), lower := (rows 7 42 196 266 112 33 65 128 256), losses := [] }

theorem u1389 : Upper (D 6) (R 6) [6,40,192,258,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1389
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1390 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 42 196 266 112 33 68 145 273), lower := (rows 7 42 196 266 112 33 68 128 256), losses := [] }

theorem u1390 : Upper (D 6) (R 6) [6,40,192,258,96,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1390
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1391 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 299, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 196 266 112 33 80 133 261), lower := (rows 7 42 196 266 112 33 80 128 256), losses := [] }

theorem u1391 : Upper (D 6) (R 6) [6,40,192,258,96,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1391
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1392 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 42 196 268 81 48 65 162 290), lower := (rows 7 42 196 268 81 48 65 128 256), losses := [] }

theorem u1392 : Upper (D 6) (R 6) [6,40,192,260,65,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1392
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1393 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 42 196 268 81 48 66 161 289), lower := (rows 7 42 196 268 81 48 66 128 256), losses := [] }

theorem u1393 : Upper (D 6) (R 6) [6,40,192,260,65,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1393
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1394 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 264, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 7 42 196 268 81 48 96 131 259), lower := (rows 7 42 196 268 81 48 96 128 256), losses := [] }

theorem u1394 : Upper (D 6) (R 6) [6,40,192,260,65,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1394
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1395 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,2),(4,5)], upper := (rows 7 42 196 268 82 48 65 161 289), lower := (rows 7 42 196 268 82 48 65 128 256), losses := [] }

theorem u1395 : Upper (D 6) (R 6) [6,40,192,260,66,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1395
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1396 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 114, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 268 82 48 96 129 257), lower := (rows 7 42 196 268 82 48 96 128 256), losses := [] }

theorem u1396 : Upper (D 6) (R 6) [6,40,192,260,66,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1396
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1397 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 42 196 280 81 36 65 162 290), lower := (rows 7 42 196 280 81 36 65 128 256), losses := [] }

theorem u1397 : Upper (D 6) (R 6) [6,40,192,272,65,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1397
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1398 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 164, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 7 42 196 280 81 36 66 161 289), lower := (rows 7 42 196 280 81 36 66 128 256), losses := [] }

theorem u1398 : Upper (D 6) (R 6) [6,40,192,272,65,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1398
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1399 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 100, targets := 3 },{ cop := 0, region := 112, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 42 196 280 81 36 96 131 259), lower := (rows 7 42 196 280 81 36 96 128 256), losses := [] }

theorem u1399 : Upper (D 6) (R 6) [6,40,192,272,65,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1399
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1400 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 7 42 196 280 82 33 65 164 292), lower := (rows 7 42 196 280 82 33 65 128 256), losses := [] }

theorem u1400 : Upper (D 6) (R 6) [6,40,192,272,66,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1400
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1401 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 42 196 280 82 33 68 161 289), lower := (rows 7 42 196 280 82 33 68 128 256), losses := [] }

theorem u1401 : Upper (D 6) (R 6) [6,40,192,272,66,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1401
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1402 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 196 280 82 33 96 133 261), lower := (rows 7 42 196 280 82 33 96 128 256), losses := [] }

theorem u1402 : Upper (D 6) (R 6) [6,40,192,272,66,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1402
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1403 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 7 42 196 280 82 36 65 161 289), lower := (rows 7 42 196 280 82 36 65 128 256), losses := [] }

theorem u1403 : Upper (D 6) (R 6) [6,40,192,272,66,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1403
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1404 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 196 280 82 36 96 129 257), lower := (rows 7 42 196 280 82 36 96 128 256), losses := [] }

theorem u1404 : Upper (D 6) (R 6) [6,40,192,272,66,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1404
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1405 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 42 196 280 112 33 65 134 262), lower := (rows 7 42 196 280 112 33 65 128 256), losses := [] }

theorem u1405 : Upper (D 6) (R 6) [6,40,192,272,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1405
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1406 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(4,0),(4,2)], upper := (rows 7 42 196 280 112 33 66 133 261), lower := (rows 7 42 196 280 112 33 66 128 256), losses := [] }

theorem u1406 : Upper (D 6) (R 6) [6,40,192,272,96,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1406
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1407 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 42 196 280 112 33 68 131 259), lower := (rows 7 42 196 280 112 33 68 128 256), losses := [] }

theorem u1407 : Upper (D 6) (R 6) [6,40,192,272,96,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1407
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1408 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 48, targets := 2 },{ cop := 0, region := 48, targets := 64 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 42 196 328 52 33 65 146 274), lower := (rows 7 42 196 328 52 33 65 128 256), losses := [{ target := 2, region := (rows 1 26 0 24 16 97 97 144 272), good := (rows 99 106 224 362 506 97 97 128 256) }] }

theorem u1408 : Upper (D 6) (R 6) [6,40,192,320,36,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1408
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1409 : Route 9 := (fun mask => (mask,id))

def c1409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1409 : Upper (D 6) (R 6) [6,40,192,320,36,1,2] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,36,1,2] 13 (by decide) (choices 1) [1,16] r1409 c1409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u88
  · exact u89

def b1410 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 48, targets := 2 },{ cop := 0, region := 48, targets := 64 }], pairs := [(4,1),(4,6)], upper := (rows 7 42 196 328 52 33 80 131 259), lower := (rows 7 42 196 328 52 33 80 128 256), losses := [] }

theorem u1410 : Upper (D 6) (R 6) [6,40,192,320,36,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1410
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1411 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 106, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 388 74 84 33 65 176 304), lower := (rows 7 42 388 74 84 33 65 128 256), losses := [] }

theorem u1411 : Upper (D 6) (R 6) [6,40,384,66,68,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1411
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1412 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 42 388 74 84 33 80 161 289), lower := (rows 7 42 388 74 84 33 80 128 256), losses := [] }

theorem u1412 : Upper (D 6) (R 6) [6,40,384,66,68,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1412
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1413 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 74, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 388 74 84 33 96 145 273), lower := (rows 7 42 388 74 84 33 96 128 256), losses := [] }

theorem u1413 : Upper (D 6) (R 6) [6,40,384,66,68,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1413
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1414 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 98 133 25 274 36 72 224 352), lower := (rows 7 98 133 25 274 36 72 128 256), losses := [] }

theorem u1414 : Upper (D 6) (R 6) [6,96,129,17,258,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1414
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1415 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 25 274 40 96 196 324), lower := (rows 7 98 133 25 274 40 96 128 256), losses := [] }

theorem u1415 : Upper (D 6) (R 6) [6,96,129,17,258,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1415
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1416 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 98, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 25 276 34 72 224 352), lower := (rows 7 98 133 25 276 34 72 128 256), losses := [] }

theorem u1416 : Upper (D 6) (R 6) [6,96,129,17,260,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1416
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1417 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 133 25 276 34 96 200 328), lower := (rows 7 98 133 25 276 34 96 128 256), losses := [] }

theorem u1417 : Upper (D 6) (R 6) [6,96,129,17,260,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1417
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1418 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 66, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 25 304 36 66 200 328), lower := (rows 7 98 133 25 304 36 66 128 256), losses := [{ target := 0, region := (rows 0 63 4 8 24 37 127 136 264), good := (rows 102 98 230 506 370 102 66 128 256) }] }

theorem u1418 : Upper (D 6) (R 6) [6,96,129,17,288,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1418
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1419 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 98 133 25 304 36 72 194 322), lower := (rows 7 98 133 25 304 36 72 128 256), losses := [] }

theorem u1419 : Upper (D 6) (R 6) [6,96,129,17,288,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1419
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1420 : PairBound 9 := { available := 96, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 98 133 26 273 36 72 224 352), lower := (rows 7 98 133 26 273 36 72 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 88 146 274), good := (rows 422 482 164 474 506 36 72 128 256) }] }

theorem u1420 : Upper (D 6) (R 6) [6,96,129,18,257,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1420
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1421 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 133 26 273 36 96 200 328), lower := (rows 7 98 133 26 273 36 96 128 256), losses := [] }

theorem u1421 : Upper (D 6) (R 6) [6,96,129,18,257,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1421
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1422 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 26 273 40 96 196 324), lower := (rows 7 98 133 26 273 40 96 128 256), losses := [] }

theorem u1422 : Upper (D 6) (R 6) [6,96,129,18,257,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1422
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1423 : PairBound 9 := { available := 96, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 98 133 26 276 33 72 224 352), lower := (rows 7 98 133 26 276 33 72 128 256), losses := [{ target := 0, region := (rows 0 34 4 41 17 32 111 162 290), good := (rows 478 490 220 474 340 506 72 128 256) }] }

theorem u1423 : Upper (D 6) (R 6) [6,96,129,18,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1423
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1424 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 26 276 40 96 193 321), lower := (rows 7 98 133 26 276 40 96 128 256), losses := [] }

theorem u1424 : Upper (D 6) (R 6) [6,96,129,18,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1424
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1425 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 280, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 98 133 26 280 33 68 224 352), lower := (rows 7 98 133 26 280 33 68 128 256), losses := [] }

theorem u1425 : Upper (D 6) (R 6) [6,96,129,18,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1425
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1426 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 133 26 280 33 96 196 324), lower := (rows 7 98 133 26 280 33 96 128 256), losses := [] }

theorem u1426 : Upper (D 6) (R 6) [6,96,129,18,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1426
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1427 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 133 26 280 36 96 193 321), lower := (rows 7 98 133 26 280 36 96 128 256), losses := [] }

theorem u1427 : Upper (D 6) (R 6) [6,96,129,18,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1427
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1428 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 280, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 98 133 26 304 36 65 200 328), lower := (rows 7 98 133 26 304 36 65 128 256), losses := [] }

theorem u1428 : Upper (D 6) (R 6) [6,96,129,18,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1428
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1429 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 74, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 26 304 36 72 193 321), lower := (rows 7 98 133 26 304 36 72 128 256), losses := [] }

theorem u1429 : Upper (D 6) (R 6) [6,96,129,18,288,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1429
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1430 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 98, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 28 273 34 72 224 352), lower := (rows 7 98 133 28 273 34 72 128 256), losses := [] }

theorem u1430 : Upper (D 6) (R 6) [6,96,129,20,257,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1430
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1431 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 133 28 273 34 96 200 328), lower := (rows 7 98 133 28 273 34 96 128 256), losses := [] }

theorem u1431 : Upper (D 6) (R 6) [6,96,129,20,257,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1431
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1432 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 98 133 28 274 33 72 224 352), lower := (rows 7 98 133 28 274 33 72 128 256), losses := [] }

theorem u1432 : Upper (D 6) (R 6) [6,96,129,20,258,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1432
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1433 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 28 274 40 96 193 321), lower := (rows 7 98 133 28 274 40 96 128 256), losses := [] }

theorem u1433 : Upper (D 6) (R 6) [6,96,129,20,258,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1433
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1434 : PairBound 9 := { available := 72, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 133 28 304 34 65 200 328), lower := (rows 7 98 133 28 304 34 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 9 82 99 64 192 320), good := (rows 62 498 172 28 304 50 506 128 256) }] }

theorem u1434 : Upper (D 6) (R 6) [6,96,129,20,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1434
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1435 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 28 304 34 72 193 321), lower := (rows 7 98 133 28 304 34 72 128 256), losses := [] }

theorem u1435 : Upper (D 6) (R 6) [6,96,129,20,288,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1435
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1436 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 41 84 288 66 152 280), lower := (rows 7 98 133 41 84 288 66 128 256), losses := [] }

theorem u1436 : Upper (D 6) (R 6) [6,96,129,33,68,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1436
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1437 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 149, targets := 32 }], pairs := [(0,5)], upper := (rows 7 98 133 41 84 288 72 146 274), lower := (rows 7 98 133 41 84 288 72 128 256), losses := [] }

theorem u1437 : Upper (D 6) (R 6) [6,96,129,33,68,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1437
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1438 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 133 41 84 288 80 138 266), lower := (rows 7 98 133 41 84 288 80 128 256), losses := [] }

theorem u1438 : Upper (D 6) (R 6) [6,96,129,33,68,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1438
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1439 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 41 88 288 66 148 276), lower := (rows 7 98 133 41 88 288 66 128 256), losses := [] }

theorem u1439 : Upper (D 6) (R 6) [6,96,129,33,72,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1439
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1439
end Delivery.IrregularNine14.P06
