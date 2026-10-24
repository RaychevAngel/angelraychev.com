import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0003

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1380 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 261 137 176 96 89 153 281), lower := (rows 35 70 261 137 176 96 64 128 256), losses := [] }

theorem u1380 : Upper (D 3) (R 3) [34,68,257,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1380
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1381 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 261 137 208 33 120 184 312), lower := (rows 35 70 261 137 208 33 64 128 256), losses := [] }

theorem u1381 : Upper (D 3) (R 3) [34,68,257,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1381
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1382 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 70 261 137 208 40 113 177 305), lower := (rows 35 70 261 137 208 40 64 128 256), losses := [] }

theorem u1382 : Upper (D 3) (R 3) [34,68,257,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1382
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1383 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 70 261 137 208 48 105 169 297), lower := (rows 35 70 261 137 208 48 64 128 256), losses := [] }

theorem u1383 : Upper (D 3) (R 3) [34,68,257,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1383
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1384 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 261 168 208 33 89 153 281), lower := (rows 35 70 261 168 208 33 64 128 256), losses := [] }

theorem u1384 : Upper (D 3) (R 3) [34,68,257,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1384
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1385 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 70 261 168 208 40 81 145 273), lower := (rows 35 70 261 168 208 40 64 128 256), losses := [] }

theorem u1385 : Upper (D 3) (R 3) [34,68,257,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1385
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1386 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 70 261 168 208 48 73 137 265), lower := (rows 35 70 261 168 208 48 64 128 256), losses := [] }

theorem u1386 : Upper (D 3) (R 3) [34,68,257,160,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1386
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1387 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 268 137 112 33 209 145 401), lower := (rows 35 70 268 137 112 33 64 128 256), losses := [] }

theorem u1387 : Upper (D 3) (R 3) [34,68,264,129,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1387
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1388 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 268 137 112 48 193 129 385), lower := (rows 35 70 268 137 112 48 64 128 256), losses := [] }

theorem u1388 : Upper (D 3) (R 3) [34,68,264,129,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1388
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1389 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 268 137 112 160 81 145 273), lower := (rows 35 70 268 137 112 160 64 128 256), losses := [] }

theorem u1389 : Upper (D 3) (R 3) [34,68,264,129,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1389
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1390 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 137 176 33 81 209 337), lower := (rows 35 70 268 137 176 33 64 128 256), losses := [] }

theorem u1390 : Upper (D 3) (R 3) [34,68,264,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1390
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1391 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 70 268 137 176 48 65 193 321), lower := (rows 35 70 268 137 176 48 64 128 256), losses := [] }

theorem u1391 : Upper (D 3) (R 3) [34,68,264,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1391
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1392 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 268 137 176 96 81 145 273), lower := (rows 35 70 268 137 176 96 64 128 256), losses := [] }

theorem u1392 : Upper (D 3) (R 3) [34,68,264,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1392
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1393 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 137 208 33 113 177 305), lower := (rows 35 70 268 137 208 33 64 128 256), losses := [] }

theorem u1393 : Upper (D 3) (R 3) [34,68,264,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1393
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1394 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 268 137 208 48 97 161 289), lower := (rows 35 70 268 137 208 48 64 128 256), losses := [] }

theorem u1394 : Upper (D 3) (R 3) [34,68,264,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1394
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1395 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 56 208 33 73 137 265), lower := (rows 35 70 388 56 208 33 64 128 256), losses := [] }

theorem u1395 : Upper (D 3) (R 3) [34,68,384,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1395
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1396 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 70 388 56 208 40 65 129 257), lower := (rows 35 70 388 56 208 40 64 128 256), losses := [] }

theorem u1396 : Upper (D 3) (R 3) [34,68,384,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1396
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1397 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 88 176 33 73 137 265), lower := (rows 35 70 388 88 176 33 64 128 256), losses := [] }

theorem u1397 : Upper (D 3) (R 3) [34,68,384,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1397
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1398 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 70 388 88 176 40 65 129 257), lower := (rows 35 70 388 88 176 40 64 128 256), losses := [] }

theorem u1398 : Upper (D 3) (R 3) [34,68,384,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1398
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1399 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 388 104 152 33 81 145 273), lower := (rows 35 70 388 104 152 33 64 128 256), losses := [] }

theorem u1399 : Upper (D 3) (R 3) [34,68,384,96,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1399
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1400 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 70 388 104 152 48 65 129 257), lower := (rows 35 70 388 104 152 48 64 128 256), losses := [] }

theorem u1400 : Upper (D 3) (R 3) [34,68,384,96,136,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1400
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1401 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 13 268 112 33 209 145 401), lower := (rows 35 194 13 268 112 33 64 128 256), losses := [] }

theorem u1401 : Upper (D 3) (R 3) [34,192,9,260,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1401
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1402 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 194 13 268 112 48 193 129 385), lower := (rows 35 194 13 268 112 48 64 128 256), losses := [] }

theorem u1402 : Upper (D 3) (R 3) [34,192,9,260,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1402
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1403 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 13 268 112 160 81 145 273), lower := (rows 35 194 13 268 112 160 64 128 256), losses := [] }

theorem u1403 : Upper (D 3) (R 3) [34,192,9,260,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1403
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1404 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 28 104 273 33 197 133 389), lower := (rows 35 194 28 104 273 33 64 128 256), losses := [] }

theorem u1404 : Upper (D 3) (R 3) [34,192,24,96,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1404
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1405 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 194 28 104 273 36 193 129 385), lower := (rows 35 194 28 104 273 36 64 128 256), losses := [] }

theorem u1405 : Upper (D 3) (R 3) [34,192,24,96,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1405
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1406 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 28 104 273 160 69 133 261), lower := (rows 35 194 28 104 273 160 64 128 256), losses := [] }

theorem u1406 : Upper (D 3) (R 3) [34,192,24,96,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1406
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1407 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 28 104 400 33 69 133 261), lower := (rows 35 194 28 104 400 33 64 128 256), losses := [] }

theorem u1407 : Upper (D 3) (R 3) [34,192,24,96,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1407
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1408 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 194 28 104 400 36 65 129 257), lower := (rows 35 194 28 104 400 36 64 128 256), losses := [] }

theorem u1408 : Upper (D 3) (R 3) [34,192,24,96,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1408
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1409 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 88 273 33 197 133 389), lower := (rows 35 194 44 88 273 33 64 128 256), losses := [] }

theorem u1409 : Upper (D 3) (R 3) [34,192,40,80,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1409
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1410 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 194 44 88 273 36 193 129 385), lower := (rows 35 194 44 88 273 36 64 128 256), losses := [] }

theorem u1410 : Upper (D 3) (R 3) [34,192,40,80,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1410
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1411 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 44 88 273 160 69 133 261), lower := (rows 35 194 44 88 273 160 64 128 256), losses := [] }

theorem u1411 : Upper (D 3) (R 3) [34,192,40,80,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1411
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1412 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 88 400 33 69 133 261), lower := (rows 35 194 44 88 400 33 64 128 256), losses := [] }

theorem u1412 : Upper (D 3) (R 3) [34,192,40,80,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1412
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1413 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 194 44 88 400 36 65 129 257), lower := (rows 35 194 44 88 400 36 64 128 256), losses := [] }

theorem u1413 : Upper (D 3) (R 3) [34,192,40,80,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1413
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1414 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 265 84 33 209 145 401), lower := (rows 35 194 44 265 84 33 64 128 256), losses := [] }

theorem u1414 : Upper (D 3) (R 3) [34,192,40,257,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1414
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1415 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 194 44 265 84 48 193 129 385), lower := (rows 35 194 44 265 84 48 64 128 256), losses := [] }

theorem u1415 : Upper (D 3) (R 3) [34,192,40,257,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1415
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1416 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 44 265 84 160 81 145 273), lower := (rows 35 194 44 265 84 160 64 128 256), losses := [] }

theorem u1416 : Upper (D 3) (R 3) [34,192,40,257,68,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1416
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1417 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 328 148 33 81 145 273), lower := (rows 35 194 44 328 148 33 64 128 256), losses := [] }

theorem u1417 : Upper (D 3) (R 3) [34,192,40,320,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1417
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1418 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 194 44 328 148 48 65 129 257), lower := (rows 35 194 44 328 148 48 64 128 256), losses := [] }

theorem u1418 : Upper (D 3) (R 3) [34,192,40,320,132,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1418
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1419 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 152 273 33 101 165 293), lower := (rows 35 194 76 152 273 33 64 128 256), losses := [] }

theorem u1419 : Upper (D 3) (R 3) [34,192,72,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1419
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1420 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 194 76 152 273 36 97 161 289), lower := (rows 35 194 76 152 273 36 64 128 256), losses := [] }

theorem u1420 : Upper (D 3) (R 3) [34,192,72,144,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1420
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1421 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 152 304 33 69 133 261), lower := (rows 35 194 76 152 304 33 64 128 256), losses := [] }

theorem u1421 : Upper (D 3) (R 3) [34,192,72,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1421
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1422 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 194 76 152 304 36 65 129 257), lower := (rows 35 194 76 152 304 36 64 128 256), losses := [] }

theorem u1422 : Upper (D 3) (R 3) [34,192,72,144,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1422
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1423 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 168 273 33 85 149 277), lower := (rows 35 194 76 168 273 33 64 128 256), losses := [] }

theorem u1423 : Upper (D 3) (R 3) [34,192,72,160,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1423
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1424 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 194 76 168 273 36 81 145 273), lower := (rows 35 194 76 168 273 36 64 128 256), losses := [] }

theorem u1424 : Upper (D 3) (R 3) [34,192,72,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1424
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1425 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 194 76 168 273 48 69 133 261), lower := (rows 35 194 76 168 273 48 64 128 256), losses := [] }

theorem u1425 : Upper (D 3) (R 3) [34,192,72,160,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1425
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1426 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 168 276 33 81 145 273), lower := (rows 35 194 76 168 276 33 64 128 256), losses := [] }

theorem u1426 : Upper (D 3) (R 3) [34,192,72,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1426
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1427 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 194 76 168 276 48 65 129 257), lower := (rows 35 194 76 168 276 48 64 128 256), losses := [] }

theorem u1427 : Upper (D 3) (R 3) [34,192,72,160,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1427
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1428 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 265 176 33 85 149 277), lower := (rows 35 194 76 265 176 33 64 128 256), losses := [] }

theorem u1428 : Upper (D 3) (R 3) [34,192,72,257,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1428
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1429 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 194 76 265 176 36 81 145 273), lower := (rows 35 194 76 265 176 36 64 128 256), losses := [] }

theorem u1429 : Upper (D 3) (R 3) [34,192,72,257,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1429
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1430 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 194 76 265 176 48 69 133 261), lower := (rows 35 194 76 265 176 48 64 128 256), losses := [] }

theorem u1430 : Upper (D 3) (R 3) [34,192,72,257,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1430
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1431 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 280 176 33 69 133 261), lower := (rows 35 194 76 280 176 33 64 128 256), losses := [] }

theorem u1431 : Upper (D 3) (R 3) [34,192,72,272,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1431
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1432 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 194 76 280 176 36 65 129 257), lower := (rows 35 194 76 280 176 36 64 128 256), losses := [] }

theorem u1432 : Upper (D 3) (R 3) [34,192,72,272,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1432
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1433 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 28 208 33 224 224 480), lower := (rows 35 259 13 28 208 33 64 128 256), losses := [] }

theorem u1433 : Upper (D 3) (R 3) [34,257,9,20,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1433
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1434 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 28 208 96 225 161 417), lower := (rows 35 259 13 28 208 96 64 128 256), losses := [] }

theorem u1434 : Upper (D 3) (R 3) [34,257,9,20,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1434
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1435 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 259 13 76 145 48 224 224 480), lower := (rows 35 259 13 76 145 48 64 128 256), losses := [] }

theorem u1435 : Upper (D 3) (R 3) [34,257,9,68,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1435
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1436 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 403, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 76 145 96 240 176 432), lower := (rows 35 259 13 76 145 96 64 128 256), losses := [] }

theorem u1436 : Upper (D 3) (R 3) [34,257,9,68,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1436
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1437 : Route 9 := (fun mask => (mask,id))

def c1437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1437 : Upper (D 3) (R 3) [34,257,9,68,129,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,68,129,128] 13 (by decide) (choices 1) [16,32] r1437 c1437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u227
  · exact u228

def b1438 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 76 176 33 208 208 464), lower := (rows 35 259 13 76 176 33 64 128 256), losses := [] }

theorem u1438 : Upper (D 3) (R 3) [34,257,9,68,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1438
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1439 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 259 13 76 176 48 193 193 449), lower := (rows 35 259 13 76 176 48 64 128 256), losses := [] }

theorem u1439 : Upper (D 3) (R 3) [34,257,9,68,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1439
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1439
end Delivery.IrregularNine14.P03
