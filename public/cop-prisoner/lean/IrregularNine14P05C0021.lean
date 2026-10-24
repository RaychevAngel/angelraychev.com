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

def b1260 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 392 25 40 68 161 289), lower := (rows 19 70 38 392 25 40 68 128 256), losses := [] }

theorem u1260 : Upper (D 5) (R 5) [18,68,34,384,9,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1260
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1261 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 70, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 392 25 40 96 133 261), lower := (rows 19 70 38 392 25 40 96 128 256), losses := [] }

theorem u1261 : Upper (D 5) (R 5) [18,68,34,384,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1261
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1262 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 392, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 38 392 56 33 65 140 268), lower := (rows 19 70 38 392 56 33 65 128 256), losses := [] }

theorem u1262 : Upper (D 5) (R 5) [18,68,34,384,40,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1262
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1263 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 392, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 392 56 33 68 137 265), lower := (rows 19 70 38 392 56 33 68 128 256), losses := [] }

theorem u1263 : Upper (D 5) (R 5) [18,68,34,384,40,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1263
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1264 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 70, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 392 56 33 72 133 261), lower := (rows 19 70 38 392 56 33 72 128 256), losses := [] }

theorem u1264 : Upper (D 5) (R 5) [18,68,34,384,40,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1264
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1265 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 44 137 280 34 65 164 292), lower := (rows 19 70 44 137 280 34 65 128 256), losses := [] }

theorem u1265 : Upper (D 5) (R 5) [18,68,40,129,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1265
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1266 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 70 44 137 280 34 68 161 289), lower := (rows 19 70 44 137 280 34 68 128 256), losses := [] }

theorem u1266 : Upper (D 5) (R 5) [18,68,40,129,264,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1266
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1267 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 70 44 137 280 34 96 133 261), lower := (rows 19 70 44 137 280 34 96 128 256), losses := [] }

theorem u1267 : Upper (D 5) (R 5) [18,68,40,129,264,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1267
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1268 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 44 137 304 34 65 140 268), lower := (rows 19 70 44 137 304 34 65 128 256), losses := [] }

theorem u1268 : Upper (D 5) (R 5) [18,68,40,129,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1268
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1269 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 70 44 137 304 34 68 137 265), lower := (rows 19 70 44 137 304 34 68 128 256), losses := [] }

theorem u1269 : Upper (D 5) (R 5) [18,68,40,129,288,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1269
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1270 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 305, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 44 137 304 34 72 133 261), lower := (rows 19 70 44 137 304 34 72 128 256), losses := [] }

theorem u1270 : Upper (D 5) (R 5) [18,68,40,129,288,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1270
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1271 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 83, targets := 8 }], pairs := [(0,3)], upper := (rows 19 70 44 138 49 288 65 140 268), lower := (rows 19 70 44 138 49 288 65 128 256), losses := [] }

theorem u1271 : Upper (D 5) (R 5) [18,68,40,130,33,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1271
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1272 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2)], upper := (rows 19 70 44 138 49 288 68 137 265), lower := (rows 19 70 44 138 49 288 68 128 256), losses := [] }

theorem u1272 : Upper (D 5) (R 5) [18,68,40,130,33,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1272
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1273 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 305, targets := 8 }], pairs := [(0,3)], upper := (rows 19 70 44 138 49 288 72 133 261), lower := (rows 19 70 44 138 49 288 72 128 256), losses := [] }

theorem u1273 : Upper (D 5) (R 5) [18,68,40,130,33,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1273
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1274 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 44 138 276 33 65 168 296), lower := (rows 19 70 44 138 276 33 65 128 256), losses := [] }

theorem u1274 : Upper (D 5) (R 5) [18,68,40,130,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1274
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1275 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 305, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 44 138 276 33 72 161 289), lower := (rows 19 70 44 138 276 33 72 128 256), losses := [] }

theorem u1275 : Upper (D 5) (R 5) [18,68,40,130,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1275
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1276 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 70 44 138 276 33 96 137 265), lower := (rows 19 70 44 138 276 33 96 128 256), losses := [] }

theorem u1276 : Upper (D 5) (R 5) [18,68,40,130,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1276
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1277 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 44 138 280 33 65 164 292), lower := (rows 19 70 44 138 280 33 65 128 256), losses := [] }

theorem u1277 : Upper (D 5) (R 5) [18,68,40,130,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1277
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1278 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 70 44 138 280 33 68 161 289), lower := (rows 19 70 44 138 280 33 68 128 256), losses := [] }

theorem u1278 : Upper (D 5) (R 5) [18,68,40,130,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1278
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1279 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 70 44 138 280 33 96 133 261), lower := (rows 19 70 44 138 280 33 96 128 256), losses := [] }

theorem u1279 : Upper (D 5) (R 5) [18,68,40,130,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1279
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1280 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 136, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 19 70 44 138 304 33 65 140 268), lower := (rows 19 70 44 138 304 33 65 128 256), losses := [] }

theorem u1280 : Upper (D 5) (R 5) [18,68,40,130,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1280
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1281 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 70 44 138 304 33 68 137 265), lower := (rows 19 70 44 138 304 33 68 128 256), losses := [] }

theorem u1281 : Upper (D 5) (R 5) [18,68,40,130,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1281
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1282 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 305, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 44 138 304 33 72 133 261), lower := (rows 19 70 44 138 304 33 72 128 256), losses := [] }

theorem u1282 : Upper (D 5) (R 5) [18,68,40,130,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1282
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1283 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 44 140 25 34 65 416 288), lower := (rows 19 70 44 140 25 34 65 128 256), losses := [] }

theorem u1283 : Upper (D 5) (R 5) [18,68,40,132,9,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1283
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1284 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 70 44 140 25 34 96 385 257), lower := (rows 19 70 44 140 25 34 96 128 256), losses := [] }

theorem u1284 : Upper (D 5) (R 5) [18,68,40,132,9,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1284
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1285 : PairBound 9 := { available := 33, camps := [], pairs := [(2,0)], upper := (rows 19 70 44 140 25 34 320 161 289), lower := (rows 19 70 44 140 25 34 320 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 35 320 128 256), good := (rows 54 102 44 140 60 34 320 128 320) }] }

theorem u1285 : Upper (D 5) (R 5) [18,68,40,132,9,2,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1285
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1286 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 83, targets := 32 }], pairs := [(0,5)], upper := (rows 19 70 44 140 25 288 65 162 290), lower := (rows 19 70 44 140 25 288 65 128 256), losses := [] }

theorem u1286 : Upper (D 5) (R 5) [18,68,40,132,9,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1286
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1287 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1)], upper := (rows 19 70 44 140 25 288 66 161 289), lower := (rows 19 70 44 140 25 288 66 128 256), losses := [] }

theorem u1287 : Upper (D 5) (R 5) [18,68,40,132,9,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1287
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1288 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 153, targets := 32 }], pairs := [(0,5)], upper := (rows 19 70 44 140 25 288 96 131 259), lower := (rows 19 70 44 140 25 288 96 128 256), losses := [] }

theorem u1288 : Upper (D 5) (R 5) [18,68,40,132,9,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1288
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1289 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 83, targets := 8 }], pairs := [(0,3)], upper := (rows 19 70 44 140 49 288 65 138 266), lower := (rows 19 70 44 140 49 288 65 128 256), losses := [] }

theorem u1289 : Upper (D 5) (R 5) [18,68,40,132,33,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1289
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1290 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1)], upper := (rows 19 70 44 140 49 288 66 137 265), lower := (rows 19 70 44 140 49 288 66 128 256), losses := [] }

theorem u1290 : Upper (D 5) (R 5) [18,68,40,132,33,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1290
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1291 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2)], upper := (rows 19 70 44 140 49 288 72 131 259), lower := (rows 19 70 44 140 49 288 72 128 256), losses := [] }

theorem u1291 : Upper (D 5) (R 5) [18,68,40,132,33,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1291
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1292 : PairBound 9 := { available := 34, camps := [], pairs := [(1,3),(1,5)], upper := (rows 19 70 44 140 280 33 65 162 290), lower := (rows 19 70 44 140 280 33 65 128 256), losses := [{ target := 3, region := (rows 1 6 4 0 16 97 97 135 263), good := (rows 499 486 486 390 272 481 481 128 256) },{ target := 5, region := (rows 1 6 4 8 16 0 97 128 256), good := (rows 83 70 78 142 280 65 65 128 256) }] }

theorem u1292 : Upper (D 5) (R 5) [18,68,40,132,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1292
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1293 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 172, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 44 140 280 33 66 161 289), lower := (rows 19 70 44 140 280 33 66 128 256), losses := [] }

theorem u1293 : Upper (D 5) (R 5) [18,68,40,132,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1293
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1294 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 70 44 140 280 33 96 131 259), lower := (rows 19 70 44 140 280 33 96 128 256), losses := [] }

theorem u1294 : Upper (D 5) (R 5) [18,68,40,132,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1294
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1295 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 136, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 19 70 44 140 304 33 65 138 266), lower := (rows 19 70 44 140 304 33 65 128 256), losses := [] }

theorem u1295 : Upper (D 5) (R 5) [18,68,40,132,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1295
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1296 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 172, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 44 140 304 33 66 137 265), lower := (rows 19 70 44 140 304 33 66 128 256), losses := [] }

theorem u1296 : Upper (D 5) (R 5) [18,68,40,132,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1296
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1297 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 44 140 304 33 72 131 259), lower := (rows 19 70 44 140 304 33 72 128 256), losses := [] }

theorem u1297 : Upper (D 5) (R 5) [18,68,40,132,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1297
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1298 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 44 392 25 34 65 164 292), lower := (rows 19 70 44 392 25 34 65 128 256), losses := [] }

theorem u1298 : Upper (D 5) (R 5) [18,68,40,384,9,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1298
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1299 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 70 44 392 25 34 68 161 289), lower := (rows 19 70 44 392 25 34 68 128 256), losses := [] }

theorem u1299 : Upper (D 5) (R 5) [18,68,40,384,9,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1299
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1300 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 70 44 392 25 34 96 133 261), lower := (rows 19 70 44 392 25 34 96 128 256), losses := [] }

theorem u1300 : Upper (D 5) (R 5) [18,68,40,384,9,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1300
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1301 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 172, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 133 41 280 36 66 168 296), lower := (rows 19 70 133 41 280 36 66 128 256), losses := [] }

theorem u1301 : Upper (D 5) (R 5) [18,68,129,33,264,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1301
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1302 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 164, targets := 8 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,3),(3,1)], upper := (rows 19 70 133 41 280 36 72 162 290), lower := (rows 19 70 133 41 280 36 72 128 256), losses := [] }

theorem u1302 : Upper (D 5) (R 5) [18,68,129,33,264,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1302
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1303 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 98, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 133 41 280 36 96 138 266), lower := (rows 19 70 133 41 280 36 96 128 256), losses := [] }

theorem u1303 : Upper (D 5) (R 5) [18,68,129,33,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1303
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1304 : Route 9 := (fun mask => (mask,id))

def c1304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1304 : Upper (D 5) (R 5) [18,68,129,34,260,1,8] 13 := by
  apply FastRouting.sound _ _ [18,68,129,34,260,1,8] 13 (by decide) (choices 1) [8,32] r1304 c1304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u66
  · exact u67

def b1305 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 19 70 133 42 276 33 96 136 264), lower := (rows 19 70 133 42 276 33 96 128 256), losses := [] }

theorem u1305 : Upper (D 5) (R 5) [18,68,129,34,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1305
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1306 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 70 133 42 280 33 68 168 296), lower := (rows 19 70 133 42 280 33 68 128 256), losses := [] }

theorem u1306 : Upper (D 5) (R 5) [18,68,129,34,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1306
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1307 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 164, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 70 133 42 280 33 72 164 292), lower := (rows 19 70 133 42 280 33 72 128 256), losses := [] }

theorem u1307 : Upper (D 5) (R 5) [18,68,129,34,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1307
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1308 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 19 70 133 42 280 33 96 140 268), lower := (rows 19 70 133 42 280 33 96 128 256), losses := [] }

theorem u1308 : Upper (D 5) (R 5) [18,68,129,34,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1308
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1309 : PairBound 9 := { available := 8, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 70 133 42 304 33 68 136 264), lower := (rows 19 70 133 42 304 33 68 128 256), losses := [] }

theorem u1309 : Upper (D 5) (R 5) [18,68,129,34,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1309
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1310 : Route 9 := (fun mask => (mask,id))

def c1310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1310 : Upper (D 5) (R 5) [18,68,129,34,288,1,8] 13 := by
  apply FastRouting.sound _ _ [18,68,129,34,288,1,8] 13 (by decide) (choices 1) [4,8] r1310 c1310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u68
  · exact u69

def b1311 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 133 44 280 34 65 168 296), lower := (rows 19 70 133 44 280 34 65 128 256), losses := [] }

theorem u1311 : Upper (D 5) (R 5) [18,68,129,36,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1311
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1312 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 106, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 133 44 280 34 72 161 289), lower := (rows 19 70 133 44 280 34 72 128 256), losses := [] }

theorem u1312 : Upper (D 5) (R 5) [18,68,129,36,264,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1312
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1313 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 106, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 133 44 280 34 96 137 265), lower := (rows 19 70 133 44 280 34 96 128 256), losses := [] }

theorem u1313 : Upper (D 5) (R 5) [18,68,129,36,264,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1313
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1314 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 133 44 304 34 65 136 264), lower := (rows 19 70 133 44 304 34 65 128 256), losses := [] }

theorem u1314 : Upper (D 5) (R 5) [18,68,129,36,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1314
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1315 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 106, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 133 44 304 34 72 137 265), lower := (rows 19 70 133 44 304 34 72 128 256), losses := [] }

theorem u1315 : Upper (D 5) (R 5) [18,68,129,36,288,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1315
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1316 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 133 265 52 40 66 168 296), lower := (rows 19 70 133 265 52 40 66 128 256), losses := [] }

theorem u1316 : Upper (D 5) (R 5) [18,68,129,257,36,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1316
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1317 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(1,0),(3,2)], upper := (rows 19 70 133 265 52 40 72 162 290), lower := (rows 19 70 133 265 52 40 72 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 18 104 104 146 274), good := (rows 402 502 132 360 502 104 104 128 256) }] }

theorem u1317 : Upper (D 5) (R 5) [18,68,129,257,36,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1317
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1318 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 70 133 265 52 40 96 138 266), lower := (rows 19 70 133 265 52 40 96 128 256), losses := [] }

theorem u1318 : Upper (D 5) (R 5) [18,68,129,257,36,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1318
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1319 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 133 265 56 36 66 168 296), lower := (rows 19 70 133 265 56 36 66 128 256), losses := [] }

theorem u1319 : Upper (D 5) (R 5) [18,68,129,257,40,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1319
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1319
end Delivery.IrregularNine14.P05
