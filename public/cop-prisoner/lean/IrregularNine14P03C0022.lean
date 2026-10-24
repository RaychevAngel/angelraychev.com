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

def b1320 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 152 273 33 104 232 360), lower := (rows 35 70 133 152 273 33 64 128 256), losses := [] }

theorem u1320 : Upper (D 3) (R 3) [34,68,129,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1320
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1321 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 133 152 273 40 97 225 353), lower := (rows 35 70 133 152 273 40 64 128 256), losses := [] }

theorem u1321 : Upper (D 3) (R 3) [34,68,129,144,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1321
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1322 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 152 273 96 105 169 297), lower := (rows 35 70 133 152 273 96 64 128 256), losses := [] }

theorem u1322 : Upper (D 3) (R 3) [34,68,129,144,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1322
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1323 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 152 304 33 73 201 329), lower := (rows 35 70 133 152 304 33 64 128 256), losses := [] }

theorem u1323 : Upper (D 3) (R 3) [34,68,129,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1323
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1324 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 70 133 152 304 40 65 193 321), lower := (rows 35 70 133 152 304 40 64 128 256), losses := [] }

theorem u1324 : Upper (D 3) (R 3) [34,68,129,144,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1324
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1325 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 152 304 96 73 137 265), lower := (rows 35 70 133 152 304 96 64 128 256), losses := [] }

theorem u1325 : Upper (D 3) (R 3) [34,68,129,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1325
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1326 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 152 336 33 105 169 297), lower := (rows 35 70 133 152 336 33 64 128 256), losses := [] }

theorem u1326 : Upper (D 3) (R 3) [34,68,129,144,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1326
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1327 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 133 152 336 40 97 161 289), lower := (rows 35 70 133 152 336 40 64 128 256), losses := [] }

theorem u1327 : Upper (D 3) (R 3) [34,68,129,144,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1327
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1328 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 168 273 33 88 216 344), lower := (rows 35 70 133 168 273 33 64 128 256), losses := [] }

theorem u1328 : Upper (D 3) (R 3) [34,68,129,160,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1328
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1329 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 70 133 168 273 40 81 209 337), lower := (rows 35 70 133 168 273 40 64 128 256), losses := [] }

theorem u1329 : Upper (D 3) (R 3) [34,68,129,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1329
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1330 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 35 70 133 168 273 48 73 201 329), lower := (rows 35 70 133 168 273 48 64 128 256), losses := [] }

theorem u1330 : Upper (D 3) (R 3) [34,68,129,160,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1330
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1331 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 168 273 96 89 153 281), lower := (rows 35 70 133 168 273 96 64 128 256), losses := [] }

theorem u1331 : Upper (D 3) (R 3) [34,68,129,160,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1331
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1332 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 168 280 33 81 209 337), lower := (rows 35 70 133 168 280 33 64 128 256), losses := [] }

theorem u1332 : Upper (D 3) (R 3) [34,68,129,160,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1332
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1333 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 70 133 168 280 48 65 193 321), lower := (rows 35 70 133 168 280 48 64 128 256), losses := [] }

theorem u1333 : Upper (D 3) (R 3) [34,68,129,160,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1333
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1334 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 168 280 96 81 145 273), lower := (rows 35 70 133 168 280 96 64 128 256), losses := [] }

theorem u1334 : Upper (D 3) (R 3) [34,68,129,160,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1334
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1335 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 168 336 33 89 153 281), lower := (rows 35 70 133 168 336 33 64 128 256), losses := [] }

theorem u1335 : Upper (D 3) (R 3) [34,68,129,160,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1335
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1336 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 70 133 168 336 40 81 145 273), lower := (rows 35 70 133 168 336 40 64 128 256), losses := [] }

theorem u1336 : Upper (D 3) (R 3) [34,68,129,160,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1336
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1337 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 70 133 168 336 48 73 137 265), lower := (rows 35 70 133 168 336 48 64 128 256), losses := [] }

theorem u1337 : Upper (D 3) (R 3) [34,68,129,160,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1337
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1338 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 200 273 33 120 184 312), lower := (rows 35 70 133 200 273 33 64 128 256), losses := [] }

theorem u1338 : Upper (D 3) (R 3) [34,68,129,192,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1338
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1339 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 70 133 200 273 40 113 177 305), lower := (rows 35 70 133 200 273 40 64 128 256), losses := [] }

theorem u1339 : Upper (D 3) (R 3) [34,68,129,192,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1339
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1340 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 70 133 200 273 48 105 169 297), lower := (rows 35 70 133 200 273 48 64 128 256), losses := [] }

theorem u1340 : Upper (D 3) (R 3) [34,68,129,192,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1340
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1341 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 200 280 33 113 177 305), lower := (rows 35 70 133 200 280 33 64 128 256), losses := [] }

theorem u1341 : Upper (D 3) (R 3) [34,68,129,192,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1341
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1342 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 133 200 280 48 97 161 289), lower := (rows 35 70 133 200 280 48 64 128 256), losses := [] }

theorem u1342 : Upper (D 3) (R 3) [34,68,129,192,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1342
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1343 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 200 304 33 89 153 281), lower := (rows 35 70 133 200 304 33 64 128 256), losses := [] }

theorem u1343 : Upper (D 3) (R 3) [34,68,129,192,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1343
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1344 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 70 133 200 304 40 81 145 273), lower := (rows 35 70 133 200 304 40 64 128 256), losses := [] }

theorem u1344 : Upper (D 3) (R 3) [34,68,129,192,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1344
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1345 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 70 133 200 304 48 73 137 265), lower := (rows 35 70 133 200 304 48 64 128 256), losses := [] }

theorem u1345 : Upper (D 3) (R 3) [34,68,129,192,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1345
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1346 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 265 112 33 209 145 401), lower := (rows 35 70 140 265 112 33 64 128 256), losses := [] }

theorem u1346 : Upper (D 3) (R 3) [34,68,136,257,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1346
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1347 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 140 265 112 48 193 129 385), lower := (rows 35 70 140 265 112 48 64 128 256), losses := [] }

theorem u1347 : Upper (D 3) (R 3) [34,68,136,257,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1347
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1348 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 140 265 112 160 81 145 273), lower := (rows 35 70 140 265 112 160 64 128 256), losses := [] }

theorem u1348 : Upper (D 3) (R 3) [34,68,136,257,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1348
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1349 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 265 176 33 81 209 337), lower := (rows 35 70 140 265 176 33 64 128 256), losses := [] }

theorem u1349 : Upper (D 3) (R 3) [34,68,136,257,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1349
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1350 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 70 140 265 176 48 65 193 321), lower := (rows 35 70 140 265 176 48 64 128 256), losses := [] }

theorem u1350 : Upper (D 3) (R 3) [34,68,136,257,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1350
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1351 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 140 265 176 96 81 145 273), lower := (rows 35 70 140 265 176 96 64 128 256), losses := [] }

theorem u1351 : Upper (D 3) (R 3) [34,68,136,257,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1351
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1352 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 265 208 33 113 177 305), lower := (rows 35 70 140 265 208 33 64 128 256), losses := [] }

theorem u1352 : Upper (D 3) (R 3) [34,68,136,257,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1352
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1353 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 140 265 208 48 97 161 289), lower := (rows 35 70 140 265 208 48 64 128 256), losses := [] }

theorem u1353 : Upper (D 3) (R 3) [34,68,136,257,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1353
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1354 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 261 25 152 33 224 224 480), lower := (rows 35 70 261 25 152 33 64 128 256), losses := [] }

theorem u1354 : Upper (D 3) (R 3) [34,68,257,17,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1354
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1355 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 261 25 152 96 225 161 417), lower := (rows 35 70 261 25 152 96 64 128 256), losses := [] }

theorem u1355 : Upper (D 3) (R 3) [34,68,257,17,136,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1355
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1356 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 261 25 152 160 97 225 353), lower := (rows 35 70 261 25 152 160 64 128 256), losses := [] }

theorem u1356 : Upper (D 3) (R 3) [34,68,257,17,136,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1356
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1357 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 261 56 145 33 200 200 456), lower := (rows 35 70 261 56 145 33 64 128 256), losses := [] }

theorem u1357 : Upper (D 3) (R 3) [34,68,257,48,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1357
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1358 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 70 261 56 145 40 193 193 449), lower := (rows 35 70 261 56 145 40 64 128 256), losses := [] }

theorem u1358 : Upper (D 3) (R 3) [34,68,257,48,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1358
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1359 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 261 56 145 96 201 137 393), lower := (rows 35 70 261 56 145 96 64 128 256), losses := [] }

theorem u1359 : Upper (D 3) (R 3) [34,68,257,48,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1359
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1360 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 261 56 145 160 73 201 329), lower := (rows 35 70 261 56 145 160 64 128 256), losses := [] }

theorem u1360 : Upper (D 3) (R 3) [34,68,257,48,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1360
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1361 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 261 56 208 33 201 137 393), lower := (rows 35 70 261 56 208 33 64 128 256), losses := [] }

theorem u1361 : Upper (D 3) (R 3) [34,68,257,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1361
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1362 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 261 56 208 40 193 129 385), lower := (rows 35 70 261 56 208 40 64 128 256), losses := [] }

theorem u1362 : Upper (D 3) (R 3) [34,68,257,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1362
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1363 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 261 56 208 160 73 137 265), lower := (rows 35 70 261 56 208 160 64 128 256), losses := [] }

theorem u1363 : Upper (D 3) (R 3) [34,68,257,48,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1363
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1364 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 261 88 145 33 232 168 424), lower := (rows 35 70 261 88 145 33 64 128 256), losses := [] }

theorem u1364 : Upper (D 3) (R 3) [34,68,257,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1364
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1365 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 261 88 145 40 225 161 417), lower := (rows 35 70 261 88 145 40 64 128 256), losses := [] }

theorem u1365 : Upper (D 3) (R 3) [34,68,257,80,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1365
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1366 : Route 9 := (fun mask => (mask,id))

def c1366 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1366 : Upper (D 3) (R 3) [34,68,257,80,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,80,129,128] 13 (by decide) (choices 1) [1,8,32] r1366 c1366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u219
  · exact u220
  · exact u221

def b1367 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 261 88 176 33 201 137 393), lower := (rows 35 70 261 88 176 33 64 128 256), losses := [] }

theorem u1367 : Upper (D 3) (R 3) [34,68,257,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1367
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1368 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 261 88 176 40 193 129 385), lower := (rows 35 70 261 88 176 40 64 128 256), losses := [] }

theorem u1368 : Upper (D 3) (R 3) [34,68,257,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1368
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1369 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 261 88 176 160 73 137 265), lower := (rows 35 70 261 88 176 160 64 128 256), losses := [] }

theorem u1369 : Upper (D 3) (R 3) [34,68,257,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1369
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1370 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 261 104 145 33 216 152 408), lower := (rows 35 70 261 104 145 33 64 128 256), losses := [] }

theorem u1370 : Upper (D 3) (R 3) [34,68,257,96,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1370
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1371 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 70 261 104 145 40 209 145 401), lower := (rows 35 70 261 104 145 40 64 128 256), losses := [] }

theorem u1371 : Upper (D 3) (R 3) [34,68,257,96,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1371
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1372 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 35 70 261 104 145 48 201 137 393), lower := (rows 35 70 261 104 145 48 64 128 256), losses := [] }

theorem u1372 : Upper (D 3) (R 3) [34,68,257,96,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1372
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1373 : Route 9 := (fun mask => (mask,id))

def c1373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1373 : Upper (D 3) (R 3) [34,68,257,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96,129,128] 13 (by decide) (choices 1) [1,8,16] r1373 c1373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u222
  · exact u223
  · exact u224

def b1374 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 261 104 152 33 209 145 401), lower := (rows 35 70 261 104 152 33 64 128 256), losses := [] }

theorem u1374 : Upper (D 3) (R 3) [34,68,257,96,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1374
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1375 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 261 104 152 48 193 129 385), lower := (rows 35 70 261 104 152 48 64 128 256), losses := [] }

theorem u1375 : Upper (D 3) (R 3) [34,68,257,96,136,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1375
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1376 : Route 9 := (fun mask => (mask,id))

def c1376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1376 : Upper (D 3) (R 3) [34,68,257,96,136,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96,136,128] 13 (by decide) (choices 1) [1,16] r1376 c1376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u225
  · exact u226

def b1377 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 261 137 176 33 88 216 344), lower := (rows 35 70 261 137 176 33 64 128 256), losses := [] }

theorem u1377 : Upper (D 3) (R 3) [34,68,257,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1377
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1378 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 70 261 137 176 40 81 209 337), lower := (rows 35 70 261 137 176 40 64 128 256), losses := [] }

theorem u1378 : Upper (D 3) (R 3) [34,68,257,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1378
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1379 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 35 70 261 137 176 48 73 201 329), lower := (rows 35 70 261 137 176 48 64 128 256), losses := [] }

theorem u1379 : Upper (D 3) (R 3) [34,68,257,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1379
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1379
end Delivery.IrregularNine14.P03
