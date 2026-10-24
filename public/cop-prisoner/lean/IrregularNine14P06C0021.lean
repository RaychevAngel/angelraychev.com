import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1260 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 133 328 81 36 80 162 290), lower := (rows 7 42 133 328 81 36 80 128 256), losses := [] }

theorem u1260 : Upper (D 6) (R 6) [6,40,129,320,65,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1260
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1261 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 112, targets := 2 }], pairs := [(1,0),(3,0),(4,1)], upper := (rows 7 42 133 328 81 36 96 146 274), lower := (rows 7 42 133 328 81 36 96 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 119 144 272), good := (rows 102 106 228 328 506 100 96 128 256) }] }

theorem u1261 : Upper (D 6) (R 6) [6,40,129,320,65,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1261
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1262 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 165, targets := 64 },{ cop := 0, region := 80, targets := 1 }], pairs := [(0,6),(2,6),(4,0)], upper := (rows 7 42 133 328 82 33 68 176 304), lower := (rows 7 42 133 328 82 33 68 128 256), losses := [] }

theorem u1262 : Upper (D 6) (R 6) [6,40,129,320,66,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1262
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1263 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 133 328 82 33 80 164 292), lower := (rows 7 42 133 328 82 33 80 128 256), losses := [] }

theorem u1263 : Upper (D 6) (R 6) [6,40,129,320,66,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1263
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1264 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 133 328 82 33 96 148 276), lower := (rows 7 42 133 328 82 33 96 128 256), losses := [] }

theorem u1264 : Upper (D 6) (R 6) [6,40,129,320,66,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1264
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1265 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 42 133 328 82 36 65 176 304), lower := (rows 7 42 133 328 82 36 65 128 256), losses := [] }

theorem u1265 : Upper (D 6) (R 6) [6,40,129,320,66,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1265
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1266 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 133 328 82 36 80 161 289), lower := (rows 7 42 133 328 82 36 80 128 256), losses := [] }

theorem u1266 : Upper (D 6) (R 6) [6,40,129,320,66,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1266
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1267 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 133 328 82 36 96 145 273), lower := (rows 7 42 133 328 82 36 96 128 256), losses := [] }

theorem u1267 : Upper (D 6) (R 6) [6,40,129,320,66,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1267
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1268 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 7 42 133 328 84 33 66 176 304), lower := (rows 7 42 133 328 84 33 66 128 256), losses := [{ target := 0, region := (rows 0 34 4 42 21 32 99 160 288), good := (rows 94 490 212 328 84 506 74 128 256) }] }

theorem u1268 : Upper (D 6) (R 6) [6,40,129,320,68,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1268
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1269 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 133 328 84 33 80 162 290), lower := (rows 7 42 133 328 84 33 80 128 256), losses := [] }

theorem u1269 : Upper (D 6) (R 6) [6,40,129,320,68,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1269
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1270 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 112, targets := 2 }], pairs := [(1,0),(3,0),(4,1)], upper := (rows 7 42 133 328 84 33 96 146 274), lower := (rows 7 42 133 328 84 33 96 128 256), losses := [{ target := 0, region := (rows 0 98 4 123 17 32 98 177 305), good := (rows 478 490 412 330 478 506 490 128 256) }] }

theorem u1270 : Upper (D 6) (R 6) [6,40,129,320,68,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1270
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1271 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 42 133 328 112 33 66 148 276), lower := (rows 7 42 133 328 112 33 66 128 256), losses := [{ target := 0, region := (rows 0 50 4 45 50 32 115 129 257), good := (rows 478 122 460 328 122 506 82 128 256) }] }

theorem u1271 : Upper (D 6) (R 6) [6,40,129,320,96,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1271
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1272 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 266, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 328 112 33 68 146 274), lower := (rows 7 42 133 328 112 33 68 128 256), losses := [] }

theorem u1272 : Upper (D 6) (R 6) [6,40,129,320,96,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1272
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1273 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 133 328 112 33 80 134 262), lower := (rows 7 42 133 328 112 33 80 128 256), losses := [] }

theorem u1273 : Upper (D 6) (R 6) [6,40,129,320,96,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1273
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1274 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 266, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 328 112 36 65 146 274), lower := (rows 7 42 133 328 112 36 65 128 256), losses := [] }

theorem u1274 : Upper (D 6) (R 6) [6,40,129,320,96,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1274
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1275 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(1,2),(4,0),(4,2)], upper := (rows 7 42 133 328 112 36 66 145 273), lower := (rows 7 42 133 328 112 36 66 128 256), losses := [{ target := 2, region := (rows 1 34 0 13 50 32 115 129 257), good := (rows 475 122 457 328 114 122 82 128 256) }] }

theorem u1275 : Upper (D 6) (R 6) [6,40,129,320,96,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1275
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1276 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 133 328 112 36 80 131 259), lower := (rows 7 42 133 328 112 36 80 128 256), losses := [] }

theorem u1276 : Upper (D 6) (R 6) [6,40,129,320,96,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1276
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1277 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 42 148 73 336 36 65 162 290), lower := (rows 7 42 148 73 336 36 65 128 256), losses := [] }

theorem u1277 : Upper (D 6) (R 6) [6,40,144,65,320,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1277
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1278 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 72, targets := 36 },{ cop := 3, region := 436, targets := 2 }], pairs := [(2,1),(3,2),(3,5)], upper := (rows 7 42 148 73 336 36 66 161 289), lower := (rows 7 42 148 73 336 36 66 128 256), losses := [] }

theorem u1278 : Upper (D 6) (R 6) [6,40,144,65,320,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1278
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1279 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 104, targets := 2 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 7 42 148 73 336 36 96 131 259), lower := (rows 7 42 148 73 336 36 96 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 111 128 256), good := (rows 102 106 244 106 336 100 96 128 256) },{ target := 2, region := (rows 1 2 0 9 25 32 98 129 257), good := (rows 475 122 144 473 336 96 96 128 256) }] }

theorem u1279 : Upper (D 6) (R 6) [6,40,144,65,320,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1279
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1280 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 42 148 74 273 33 68 224 352), lower := (rows 7 42 148 74 273 33 68 128 256), losses := [] }

theorem u1280 : Upper (D 6) (R 6) [6,40,144,66,257,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1280
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1281 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 74, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 148 74 273 33 96 196 324), lower := (rows 7 42 148 74 273 33 96 128 256), losses := [] }

theorem u1281 : Upper (D 6) (R 6) [6,40,144,66,257,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1281
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1282 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 42 148 74 273 36 65 224 352), lower := (rows 7 42 148 74 273 36 65 128 256), losses := [] }

theorem u1282 : Upper (D 6) (R 6) [6,40,144,66,257,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1282
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1283 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 74, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 148 74 273 36 96 193 321), lower := (rows 7 42 148 74 273 36 96 128 256), losses := [] }

theorem u1283 : Upper (D 6) (R 6) [6,40,144,66,257,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1283
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1284 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 106, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 148 74 336 33 65 164 292), lower := (rows 7 42 148 74 336 33 65 128 256), losses := [] }

theorem u1284 : Upper (D 6) (R 6) [6,40,144,66,320,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1284
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1285 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 42 148 74 336 33 68 161 289), lower := (rows 7 42 148 74 336 33 68 128 256), losses := [] }

theorem u1285 : Upper (D 6) (R 6) [6,40,144,66,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1285
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1286 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 74, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 148 74 336 33 96 133 261), lower := (rows 7 42 148 74 336 33 96 128 256), losses := [] }

theorem u1286 : Upper (D 6) (R 6) [6,40,144,66,320,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1286
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1287 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 42 148 74 336 36 65 161 289), lower := (rows 7 42 148 74 336 36 65 128 256), losses := [] }

theorem u1287 : Upper (D 6) (R 6) [6,40,144,66,320,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1287
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1288 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 74, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 148 74 336 36 96 129 257), lower := (rows 7 42 148 74 336 36 96 128 256), losses := [] }

theorem u1288 : Upper (D 6) (R 6) [6,40,144,66,320,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1288
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1289 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 114, targets := 4 },{ cop := 4, region := 164, targets := 2 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 7 42 148 265 81 96 66 164 292), lower := (rows 7 42 148 265 81 96 66 128 256), losses := [] }

theorem u1289 : Upper (D 6) (R 6) [6,40,144,257,65,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1289
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1290 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 298, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,2),(3,2),(4,1)], upper := (rows 7 42 148 265 81 96 68 162 290), lower := (rows 7 42 148 265 81 96 68 128 256), losses := [] }

theorem u1290 : Upper (D 6) (R 6) [6,40,144,257,65,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1290
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1291 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 0, region := 264, targets := 32 }], pairs := [(3,5),(4,1),(4,2)], upper := (rows 7 42 148 265 81 96 96 134 262), lower := (rows 7 42 148 265 81 96 96 128 256), losses := [] }

theorem u1291 : Upper (D 6) (R 6) [6,40,144,257,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1291
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1292 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 114, targets := 4 },{ cop := 4, region := 164, targets := 1 }], pairs := [(1,2),(2,0),(4,2)], upper := (rows 7 42 148 265 82 96 65 164 292), lower := (rows 7 42 148 265 82 96 65 128 256), losses := [] }

theorem u1292 : Upper (D 6) (R 6) [6,40,144,257,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1292
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1293 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 360, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,1),(4,0),(4,5)], upper := (rows 7 42 148 265 82 96 68 161 289), lower := (rows 7 42 148 265 82 96 68 128 256), losses := [] }

theorem u1293 : Upper (D 6) (R 6) [6,40,144,257,66,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1293
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1294 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 133, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 42 148 265 82 96 96 133 261), lower := (rows 7 42 148 265 82 96 96 128 256), losses := [] }

theorem u1294 : Upper (D 6) (R 6) [6,40,144,257,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1294
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1295 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,2),(3,2),(4,1)], upper := (rows 7 42 148 265 84 96 65 162 290), lower := (rows 7 42 148 265 84 96 65 128 256), losses := [] }

theorem u1295 : Upper (D 6) (R 6) [6,40,144,257,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1295
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1296 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,2),(3,2),(4,0)], upper := (rows 7 42 148 265 84 96 66 161 289), lower := (rows 7 42 148 265 84 96 66 128 256), losses := [] }

theorem u1296 : Upper (D 6) (R 6) [6,40,144,257,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1296
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1297 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 42 148 265 84 96 96 131 259), lower := (rows 7 42 148 265 84 96 96 128 256), losses := [] }

theorem u1297 : Upper (D 6) (R 6) [6,40,144,257,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1297
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1298 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 298, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 148 266 81 33 68 224 352), lower := (rows 7 42 148 266 81 33 68 128 256), losses := [] }

theorem u1298 : Upper (D 6) (R 6) [6,40,144,258,65,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1298
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1299 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 132, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 42 148 266 81 33 96 196 324), lower := (rows 7 42 148 266 81 33 96 128 256), losses := [] }

theorem u1299 : Upper (D 6) (R 6) [6,40,144,258,65,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1299
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1300 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 42 148 266 81 36 65 224 352), lower := (rows 7 42 148 266 81 36 65 128 256), losses := [] }

theorem u1300 : Upper (D 6) (R 6) [6,40,144,258,65,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1300
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1301 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 132, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 42 148 266 81 36 96 193 321), lower := (rows 7 42 148 266 81 36 96 128 256), losses := [] }

theorem u1301 : Upper (D 6) (R 6) [6,40,144,258,65,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1301
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1302 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 42 148 266 81 96 65 164 292), lower := (rows 7 42 148 266 81 96 65 128 256), losses := [] }

theorem u1302 : Upper (D 6) (R 6) [6,40,144,258,65,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1302
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1303 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 298, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 148 266 81 96 68 161 289), lower := (rows 7 42 148 266 81 96 68 128 256), losses := [] }

theorem u1303 : Upper (D 6) (R 6) [6,40,144,258,65,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1303
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1304 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 106, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 148 266 81 96 96 133 261), lower := (rows 7 42 148 266 81 96 96 128 256), losses := [] }

theorem u1304 : Upper (D 6) (R 6) [6,40,144,258,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1304
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1305 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 42 148 268 81 96 65 162 290), lower := (rows 7 42 148 268 81 96 65 128 256), losses := [] }

theorem u1305 : Upper (D 6) (R 6) [6,40,144,260,65,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1305
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1306 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 98, targets := 5 },{ cop := 4, region := 164, targets := 2 }], pairs := [(1,0),(1,2),(2,1)], upper := (rows 7 42 148 268 81 96 66 161 289), lower := (rows 7 42 148 268 81 96 66 128 256), losses := [] }

theorem u1306 : Upper (D 6) (R 6) [6,40,144,260,65,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1306
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1307 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 264, targets := 96 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(3,5),(3,6)], upper := (rows 7 42 148 268 81 96 96 131 259), lower := (rows 7 42 148 268 81 96 96 128 256), losses := [] }

theorem u1307 : Upper (D 6) (R 6) [6,40,144,260,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1307
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1308 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 360, targets := 2 },{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,1),(4,2),(4,5)], upper := (rows 7 42 148 268 82 96 65 161 289), lower := (rows 7 42 148 268 82 96 65 128 256), losses := [] }

theorem u1308 : Upper (D 6) (R 6) [6,40,144,260,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1308
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1309 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 133, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 42 148 268 82 96 96 129 257), lower := (rows 7 42 148 268 82 96 96 128 256), losses := [] }

theorem u1309 : Upper (D 6) (R 6) [6,40,144,260,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1309
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1310 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 7 42 148 328 81 33 66 164 292), lower := (rows 7 42 148 328 81 33 66 128 256), losses := [] }

theorem u1310 : Upper (D 6) (R 6) [6,40,144,320,65,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1310
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1311 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 298, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,2),(3,2),(4,1)], upper := (rows 7 42 148 328 81 33 68 162 290), lower := (rows 7 42 148 328 81 33 68 128 256), losses := [] }

theorem u1311 : Upper (D 6) (R 6) [6,40,144,320,65,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1311
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1312 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 7 42 148 328 81 33 96 134 262), lower := (rows 7 42 148 328 81 33 96 128 256), losses := [{ target := 0, region := (rows 0 98 20 57 16 32 98 145 273), good := (rows 462 106 412 330 478 490 106 128 256) }] }

theorem u1312 : Upper (D 6) (R 6) [6,40,144,320,65,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1312
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1313 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 42 148 328 81 36 65 162 290), lower := (rows 7 42 148 328 81 36 65 128 256), losses := [] }

theorem u1313 : Upper (D 6) (R 6) [6,40,144,320,65,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1313
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1314 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 164, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 7 42 148 328 81 36 66 161 289), lower := (rows 7 42 148 328 81 36 66 128 256), losses := [] }

theorem u1314 : Upper (D 6) (R 6) [6,40,144,320,65,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1314
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1315 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 112, targets := 2 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 7 42 148 328 81 36 96 131 259), lower := (rows 7 42 148 328 81 36 96 128 256), losses := [{ target := 2, region := (rows 1 2 0 25 17 32 98 129 257), good := (rows 475 106 152 328 473 96 96 128 256) }] }

theorem u1315 : Upper (D 6) (R 6) [6,40,144,320,65,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1315
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1316 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,2),(3,2),(4,1)], upper := (rows 7 42 148 328 84 33 65 162 290), lower := (rows 7 42 148 328 84 33 65 128 256), losses := [] }

theorem u1316 : Upper (D 6) (R 6) [6,40,144,320,68,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1316
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1317 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,2),(3,2),(4,0)], upper := (rows 7 42 148 328 84 33 66 161 289), lower := (rows 7 42 148 328 84 33 66 128 256), losses := [] }

theorem u1317 : Upper (D 6) (R 6) [6,40,144,320,68,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1317
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1318 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 112, targets := 2 }], pairs := [(1,2),(3,2),(4,1)], upper := (rows 7 42 148 328 84 33 96 131 259), lower := (rows 7 42 148 328 84 33 96 128 256), losses := [] }

theorem u1318 : Upper (D 6) (R 6) [6,40,144,320,68,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1318
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1319 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 42 148 328 112 33 65 134 262), lower := (rows 7 42 148 328 112 33 65 128 256), losses := [] }

theorem u1319 : Upper (D 6) (R 6) [6,40,144,320,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1319
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1319
end Delivery.IrregularNine14.P06
