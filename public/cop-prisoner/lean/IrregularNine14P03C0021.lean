import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1260 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 280 145 33 224 224 480), lower := (rows 35 70 13 280 145 33 64 128 256), losses := [] }

theorem u1260 : Upper (D 3) (R 3) [34,68,9,272,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1260
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1261 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 280 145 96 225 161 417), lower := (rows 35 70 13 280 145 96 64 128 256), losses := [] }

theorem u1261 : Upper (D 3) (R 3) [34,68,9,272,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1261
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1262 : PairBound 9 := { available := 97, camps := [], pairs := [(1,7)], upper := (rows 35 70 13 280 145 160 97 225 353), lower := (rows 35 70 13 280 145 160 64 128 256), losses := [{ target := 7, region := (rows 1 22 20 24 16 32 65 0 257), good := (rows 355 70 335 286 351 32 64 0 256) }] }

theorem u1262 : Upper (D 3) (R 3) [34,68,9,272,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1262
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1263 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 392 112 33 209 145 401), lower := (rows 35 70 13 392 112 33 64 128 256), losses := [] }

theorem u1263 : Upper (D 3) (R 3) [34,68,9,384,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1263
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1264 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 13 392 112 48 193 129 385), lower := (rows 35 70 13 392 112 48 64 128 256), losses := [] }

theorem u1264 : Upper (D 3) (R 3) [34,68,9,384,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1264
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1265 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 13 392 112 160 81 145 273), lower := (rows 35 70 13 392 112 160 64 128 256), losses := [] }

theorem u1265 : Upper (D 3) (R 3) [34,68,9,384,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1265
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1266 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 392 145 33 112 240 368), lower := (rows 35 70 13 392 145 33 64 128 256), losses := [] }

theorem u1266 : Upper (D 3) (R 3) [34,68,9,384,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1266
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1267 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 13 392 145 48 97 225 353), lower := (rows 35 70 13 392 145 48 64 128 256), losses := [] }

theorem u1267 : Upper (D 3) (R 3) [34,68,9,384,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1267
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1268 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 392 145 96 113 177 305), lower := (rows 35 70 13 392 145 96 64 128 256), losses := [] }

theorem u1268 : Upper (D 3) (R 3) [34,68,9,384,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1268
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1269 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 392 176 33 81 209 337), lower := (rows 35 70 13 392 176 33 64 128 256), losses := [] }

theorem u1269 : Upper (D 3) (R 3) [34,68,9,384,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1269
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1270 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 70 13 392 176 48 65 193 321), lower := (rows 35 70 13 392 176 48 64 128 256), losses := [] }

theorem u1270 : Upper (D 3) (R 3) [34,68,9,384,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1270
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1271 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 392 176 96 81 145 273), lower := (rows 35 70 13 392 176 96 64 128 256), losses := [] }

theorem u1271 : Upper (D 3) (R 3) [34,68,9,384,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1271
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1272 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 392 208 33 113 177 305), lower := (rows 35 70 13 392 208 33 64 128 256), losses := [] }

theorem u1272 : Upper (D 3) (R 3) [34,68,9,384,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1272
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1273 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 13 392 208 48 97 161 289), lower := (rows 35 70 13 392 208 48 64 128 256), losses := [] }

theorem u1273 : Upper (D 3) (R 3) [34,68,9,384,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1273
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1274 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 137 273 33 224 224 480), lower := (rows 35 70 28 137 273 33 64 128 256), losses := [] }

theorem u1274 : Upper (D 3) (R 3) [34,68,24,129,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1274
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1275 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 28 137 273 96 225 161 417), lower := (rows 35 70 28 137 273 96 64 128 256), losses := [] }

theorem u1275 : Upper (D 3) (R 3) [34,68,24,129,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1275
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1276 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 28 137 273 160 97 225 353), lower := (rows 35 70 28 137 273 160 64 128 256), losses := [] }

theorem u1276 : Upper (D 3) (R 3) [34,68,24,129,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1276
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1277 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 25 280 33 224 224 480), lower := (rows 35 70 133 25 280 33 64 128 256), losses := [] }

theorem u1277 : Upper (D 3) (R 3) [34,68,129,17,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1277
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1278 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 25 280 96 225 161 417), lower := (rows 35 70 133 25 280 96 64 128 256), losses := [] }

theorem u1278 : Upper (D 3) (R 3) [34,68,129,17,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1278
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1279 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 133 25 280 160 97 225 353), lower := (rows 35 70 133 25 280 160 64 128 256), losses := [] }

theorem u1279 : Upper (D 3) (R 3) [34,68,129,17,264,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1279
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1280 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 25 400 33 104 232 360), lower := (rows 35 70 133 25 400 33 64 128 256), losses := [] }

theorem u1280 : Upper (D 3) (R 3) [34,68,129,17,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1280
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1281 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 133 25 400 40 97 225 353), lower := (rows 35 70 133 25 400 40 64 128 256), losses := [] }

theorem u1281 : Upper (D 3) (R 3) [34,68,129,17,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1281
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1282 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 25 400 96 105 169 297), lower := (rows 35 70 133 25 400 96 64 128 256), losses := [] }

theorem u1282 : Upper (D 3) (R 3) [34,68,129,17,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1282
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1283 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 56 208 33 329 393 265), lower := (rows 35 70 133 56 208 33 64 128 256), losses := [] }

theorem u1283 : Upper (D 3) (R 3) [34,68,129,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1283
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1284 : PairBound 9 := { available := 257, camps := [], pairs := [], upper := (rows 35 70 133 56 208 40 321 385 257), lower := (rows 35 70 133 56 208 40 64 128 256), losses := [] }

theorem u1284 : Upper (D 3) (R 3) [34,68,129,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1284
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1285 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 70 133 56 208 288 73 137 265), lower := (rows 35 70 133 56 208 288 64 128 256), losses := [] }

theorem u1285 : Upper (D 3) (R 3) [34,68,129,48,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1285
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1286 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 56 273 33 200 200 456), lower := (rows 35 70 133 56 273 33 64 128 256), losses := [] }

theorem u1286 : Upper (D 3) (R 3) [34,68,129,48,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1286
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1287 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 70 133 56 273 40 193 193 449), lower := (rows 35 70 133 56 273 40 64 128 256), losses := [] }

theorem u1287 : Upper (D 3) (R 3) [34,68,129,48,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1287
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1288 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 56 273 96 201 137 393), lower := (rows 35 70 133 56 273 96 64 128 256), losses := [] }

theorem u1288 : Upper (D 3) (R 3) [34,68,129,48,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1288
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1289 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 133 56 273 160 73 201 329), lower := (rows 35 70 133 56 273 160 64 128 256), losses := [] }

theorem u1289 : Upper (D 3) (R 3) [34,68,129,48,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1289
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1290 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 56 336 33 201 137 393), lower := (rows 35 70 133 56 336 33 64 128 256), losses := [] }

theorem u1290 : Upper (D 3) (R 3) [34,68,129,48,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1290
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1291 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 133 56 336 40 193 129 385), lower := (rows 35 70 133 56 336 40 64 128 256), losses := [] }

theorem u1291 : Upper (D 3) (R 3) [34,68,129,48,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1291
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1292 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 133 56 336 160 73 137 265), lower := (rows 35 70 133 56 336 160 64 128 256), losses := [] }

theorem u1292 : Upper (D 3) (R 3) [34,68,129,48,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1292
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1293 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 56 400 33 73 201 329), lower := (rows 35 70 133 56 400 33 64 128 256), losses := [] }

theorem u1293 : Upper (D 3) (R 3) [34,68,129,48,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1293
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1294 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 70 133 56 400 40 65 193 321), lower := (rows 35 70 133 56 400 40 64 128 256), losses := [] }

theorem u1294 : Upper (D 3) (R 3) [34,68,129,48,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1294
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1295 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 56 400 96 73 137 265), lower := (rows 35 70 133 56 400 96 64 128 256), losses := [] }

theorem u1295 : Upper (D 3) (R 3) [34,68,129,48,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1295
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1296 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 88 176 33 329 393 265), lower := (rows 35 70 133 88 176 33 64 128 256), losses := [] }

theorem u1296 : Upper (D 3) (R 3) [34,68,129,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1296
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1297 : PairBound 9 := { available := 257, camps := [], pairs := [], upper := (rows 35 70 133 88 176 40 321 385 257), lower := (rows 35 70 133 88 176 40 64 128 256), losses := [] }

theorem u1297 : Upper (D 3) (R 3) [34,68,129,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1297
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1298 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 70 133 88 176 288 73 137 265), lower := (rows 35 70 133 88 176 288 64 128 256), losses := [] }

theorem u1298 : Upper (D 3) (R 3) [34,68,129,80,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1298
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1299 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 88 273 33 232 168 424), lower := (rows 35 70 133 88 273 33 64 128 256), losses := [] }

theorem u1299 : Upper (D 3) (R 3) [34,68,129,80,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1299
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1300 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 133 88 273 40 225 161 417), lower := (rows 35 70 133 88 273 40 64 128 256), losses := [] }

theorem u1300 : Upper (D 3) (R 3) [34,68,129,80,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1300
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1301 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 133 88 273 160 105 169 297), lower := (rows 35 70 133 88 273 160 64 128 256), losses := [] }

theorem u1301 : Upper (D 3) (R 3) [34,68,129,80,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1301
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1302 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 88 304 33 201 137 393), lower := (rows 35 70 133 88 304 33 64 128 256), losses := [] }

theorem u1302 : Upper (D 3) (R 3) [34,68,129,80,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1302
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1303 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 133 88 304 40 193 129 385), lower := (rows 35 70 133 88 304 40 64 128 256), losses := [] }

theorem u1303 : Upper (D 3) (R 3) [34,68,129,80,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1303
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1304 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 133 88 304 160 73 137 265), lower := (rows 35 70 133 88 304 160 64 128 256), losses := [] }

theorem u1304 : Upper (D 3) (R 3) [34,68,129,80,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1304
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1305 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 88 400 33 105 169 297), lower := (rows 35 70 133 88 400 33 64 128 256), losses := [] }

theorem u1305 : Upper (D 3) (R 3) [34,68,129,80,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1305
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1306 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 133 88 400 40 97 161 289), lower := (rows 35 70 133 88 400 40 64 128 256), losses := [] }

theorem u1306 : Upper (D 3) (R 3) [34,68,129,80,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1306
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1307 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 133 104 152 33 337 401 273), lower := (rows 35 70 133 104 152 33 64 128 256), losses := [] }

theorem u1307 : Upper (D 3) (R 3) [34,68,129,96,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1307
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1308 : PairBound 9 := { available := 257, camps := [], pairs := [], upper := (rows 35 70 133 104 152 48 321 385 257), lower := (rows 35 70 133 104 152 48 64 128 256), losses := [] }

theorem u1308 : Upper (D 3) (R 3) [34,68,129,96,136,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1308
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1309 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 70 133 104 152 288 81 145 273), lower := (rows 35 70 133 104 152 288 64 128 256), losses := [] }

theorem u1309 : Upper (D 3) (R 3) [34,68,129,96,136,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1309
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1310 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 133 104 273 33 216 152 408), lower := (rows 35 70 133 104 273 33 64 128 256), losses := [] }

theorem u1310 : Upper (D 3) (R 3) [34,68,129,96,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1310
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1311 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 70 133 104 273 40 209 145 401), lower := (rows 35 70 133 104 273 40 64 128 256), losses := [] }

theorem u1311 : Upper (D 3) (R 3) [34,68,129,96,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1311
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1312 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 35 70 133 104 273 48 201 137 393), lower := (rows 35 70 133 104 273 48 64 128 256), losses := [] }

theorem u1312 : Upper (D 3) (R 3) [34,68,129,96,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1312
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1313 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 133 104 273 160 89 153 281), lower := (rows 35 70 133 104 273 160 64 128 256), losses := [] }

theorem u1313 : Upper (D 3) (R 3) [34,68,129,96,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1313
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1314 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 133 104 280 33 209 145 401), lower := (rows 35 70 133 104 280 33 64 128 256), losses := [] }

theorem u1314 : Upper (D 3) (R 3) [34,68,129,96,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1314
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1315 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 133 104 280 48 193 129 385), lower := (rows 35 70 133 104 280 48 64 128 256), losses := [] }

theorem u1315 : Upper (D 3) (R 3) [34,68,129,96,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1315
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1316 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 133 104 280 160 81 145 273), lower := (rows 35 70 133 104 280 160 64 128 256), losses := [] }

theorem u1316 : Upper (D 3) (R 3) [34,68,129,96,264,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1316
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1317 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 133 104 400 33 89 153 281), lower := (rows 35 70 133 104 400 33 64 128 256), losses := [] }

theorem u1317 : Upper (D 3) (R 3) [34,68,129,96,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1317
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1318 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 70 133 104 400 40 81 145 273), lower := (rows 35 70 133 104 400 40 64 128 256), losses := [] }

theorem u1318 : Upper (D 3) (R 3) [34,68,129,96,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1318
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1319 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 70 133 104 400 48 73 137 265), lower := (rows 35 70 133 104 400 48 64 128 256), losses := [] }

theorem u1319 : Upper (D 3) (R 3) [34,68,129,96,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1319
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1319
end Delivery.IrregularNine14.P03
