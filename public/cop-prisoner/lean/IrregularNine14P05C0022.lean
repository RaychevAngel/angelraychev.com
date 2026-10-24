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

def b1320 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 164, targets := 8 }], pairs := [(1,3),(2,3)], upper := (rows 19 70 133 265 56 36 72 162 290), lower := (rows 19 70 133 265 56 36 72 128 256), losses := [{ target := 3, region := (rows 1 66 13 0 16 127 64 195 323), good := (rows 439 486 421 421 52 36 486 128 256) }] }

theorem u1320 : Upper (D 5) (R 5) [18,68,129,257,40,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1320
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1321 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 70 133 265 56 36 96 138 266), lower := (rows 19 70 133 265 56 36 96 128 256), losses := [] }

theorem u1321 : Upper (D 5) (R 5) [18,68,129,257,40,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1321
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1322 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 133 266 52 40 65 168 296), lower := (rows 19 70 133 266 52 40 65 128 256), losses := [] }

theorem u1322 : Upper (D 5) (R 5) [18,68,129,258,36,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1322
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1323 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(1,0),(3,2)], upper := (rows 19 70 133 266 52 40 72 161 289), lower := (rows 19 70 133 266 52 40 72 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 18 104 104 128 256), good := (rows 18 118 132 378 118 104 104 128 256) }] }

theorem u1323 : Upper (D 5) (R 5) [18,68,129,258,36,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1323
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1324 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 70 133 266 52 40 96 137 265), lower := (rows 19 70 133 266 52 40 96 128 256), losses := [] }

theorem u1324 : Upper (D 5) (R 5) [18,68,129,258,36,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1324
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1325 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 70 133 268 56 34 65 168 296), lower := (rows 19 70 133 268 56 34 65 128 256), losses := [] }

theorem u1325 : Upper (D 5) (R 5) [18,68,129,260,40,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1325
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1326 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 114, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 19 70 133 268 56 34 72 161 289), lower := (rows 19 70 133 268 56 34 72 128 256), losses := [] }

theorem u1326 : Upper (D 5) (R 5) [18,68,129,260,40,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1326
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1327 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 19 70 133 268 56 34 96 137 265), lower := (rows 19 70 133 268 56 34 96 128 256), losses := [] }

theorem u1327 : Upper (D 5) (R 5) [18,68,129,260,40,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1327
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1328 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 133 296 28 33 66 168 296), lower := (rows 19 70 133 296 28 33 66 128 256), losses := [] }

theorem u1328 : Upper (D 5) (R 5) [18,68,129,288,12,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1328
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1329 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 133 296 28 33 72 162 290), lower := (rows 19 70 133 296 28 33 72 128 256), losses := [] }

theorem u1329 : Upper (D 5) (R 5) [18,68,129,288,12,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1329
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1330 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 70 133 296 28 33 96 138 266), lower := (rows 19 70 133 296 28 33 96 128 256), losses := [] }

theorem u1330 : Upper (D 5) (R 5) [18,68,129,288,12,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1330
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1331 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 264, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 133 296 28 34 65 168 296), lower := (rows 19 70 133 296 28 34 65 128 256), losses := [] }

theorem u1331 : Upper (D 5) (R 5) [18,68,129,288,12,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1331
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1332 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 133 296 28 34 72 161 289), lower := (rows 19 70 133 296 28 34 72 128 256), losses := [] }

theorem u1332 : Upper (D 5) (R 5) [18,68,129,288,12,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1332
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1333 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 98, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 133 296 28 34 96 137 265), lower := (rows 19 70 133 296 28 34 96 128 256), losses := [] }

theorem u1333 : Upper (D 5) (R 5) [18,68,129,288,12,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1333
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1334 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5)], upper := (rows 19 70 134 44 25 288 65 168 296), lower := (rows 19 70 134 44 25 288 65 128 256), losses := [] }

theorem u1334 : Upper (D 5) (R 5) [18,68,130,36,9,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1334
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1335 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5)], upper := (rows 19 70 134 44 25 288 72 161 289), lower := (rows 19 70 134 44 25 288 72 128 256), losses := [] }

theorem u1335 : Upper (D 5) (R 5) [18,68,130,36,9,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1335
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1336 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 19 70 134 44 25 288 96 137 265), lower := (rows 19 70 134 44 25 288 96 128 256), losses := [] }

theorem u1336 : Upper (D 5) (R 5) [18,68,130,36,9,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1336
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1337 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 83, targets := 8 }], pairs := [(0,3)], upper := (rows 19 70 134 44 49 288 65 136 264), lower := (rows 19 70 134 44 49 288 65 128 256), losses := [] }

theorem u1337 : Upper (D 5) (R 5) [18,68,130,36,33,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1337
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1338 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 19 70 134 44 49 288 72 137 265), lower := (rows 19 70 134 44 49 288 72 128 256), losses := [] }

theorem u1338 : Upper (D 5) (R 5) [18,68,130,36,33,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1338
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1339 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 134 44 280 33 65 168 296), lower := (rows 19 70 134 44 280 33 65 128 256), losses := [] }

theorem u1339 : Upper (D 5) (R 5) [18,68,130,36,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1339
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1340 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 19 70 134 44 280 33 72 161 289), lower := (rows 19 70 134 44 280 33 72 128 256), losses := [] }

theorem u1340 : Upper (D 5) (R 5) [18,68,130,36,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1340
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1341 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 66, targets := 1 },{ cop := 3, region := 66, targets := 8 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 134 44 280 33 96 137 265), lower := (rows 19 70 134 44 280 33 96 128 256), losses := [] }

theorem u1341 : Upper (D 5) (R 5) [18,68,130,36,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1341
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1342 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 134 44 304 33 65 136 264), lower := (rows 19 70 134 44 304 33 65 128 256), losses := [] }

theorem u1342 : Upper (D 5) (R 5) [18,68,130,36,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1342
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1343 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 19 70 134 44 304 33 72 137 265), lower := (rows 19 70 134 44 304 33 72 128 256), losses := [] }

theorem u1343 : Upper (D 5) (R 5) [18,68,130,36,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1343
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1344 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 134 268 25 40 65 160 288), lower := (rows 19 70 134 268 25 40 65 128 256), losses := [] }

theorem u1344 : Upper (D 5) (R 5) [18,68,130,260,9,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1344
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1345 : Route 9 := (fun mask => (mask,id))

def c1345 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1345 : Upper (D 5) (R 5) [18,68,130,260,9,8,32] 13 := by
  apply FastRouting.sound _ _ [18,68,130,260,9,8,32] 13 (by decide) (choices 1) [1,32] r1345 c1345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u70
  · exact u71

def b1346 : PairBound 9 := { available := 40, camps := [{ cop := 6, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 134 268 49 40 65 168 296), lower := (rows 19 70 134 268 49 40 65 128 256), losses := [] }

theorem u1346 : Upper (D 5) (R 5) [18,68,130,260,33,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1346
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1347 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 66, targets := 1 },{ cop := 3, region := 66, targets := 32 }], pairs := [(1,0),(1,5)], upper := (rows 19 70 134 268 49 40 72 161 289), lower := (rows 19 70 134 268 49 40 72 128 256), losses := [] }

theorem u1347 : Upper (D 5) (R 5) [18,68,130,260,33,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1347
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1348 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 70 134 268 49 40 96 137 265), lower := (rows 19 70 134 268 49 40 96 128 256), losses := [] }

theorem u1348 : Upper (D 5) (R 5) [18,68,130,260,33,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1348
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1349 : PairBound 9 := { available := 40, camps := [], pairs := [(1,0),(2,0)], upper := (rows 19 70 134 268 56 33 65 168 296), lower := (rows 19 70 134 268 56 33 65 128 256), losses := [{ target := 0, region := (rows 0 66 5 41 48 32 64 176 304), good := (rows 414 70 134 268 440 444 78 128 256) }] }

theorem u1349 : Upper (D 5) (R 5) [18,68,130,260,40,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1349
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1350 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 19 70 134 268 56 33 72 161 289), lower := (rows 19 70 134 268 56 33 72 128 256), losses := [] }

theorem u1350 : Upper (D 5) (R 5) [18,68,130,260,40,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1350
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1351 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 70 134 268 56 33 96 137 265), lower := (rows 19 70 134 268 56 33 96 128 256), losses := [] }

theorem u1351 : Upper (D 5) (R 5) [18,68,130,260,40,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1351
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1352 : PairBound 9 := { available := 34, camps := [], pairs := [(2,0),(4,0)], upper := (rows 19 70 140 41 280 36 65 162 290), lower := (rows 19 70 140 41 280 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 62 64 131 259), good := (rows 434 486 188 444 316 36 448 128 256) }] }

theorem u1352 : Upper (D 5) (R 5) [18,68,136,33,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1352
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1353 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 172, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 140 41 280 36 66 161 289), lower := (rows 19 70 140 41 280 36 66 128 256), losses := [] }

theorem u1353 : Upper (D 5) (R 5) [18,68,136,33,264,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1353
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1354 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 98, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 140 41 280 36 96 131 259), lower := (rows 19 70 140 41 280 36 96 128 256), losses := [] }

theorem u1354 : Upper (D 5) (R 5) [18,68,136,33,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1354
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1355 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 140 42 276 33 65 168 296), lower := (rows 19 70 140 42 276 33 65 128 256), losses := [] }

theorem u1355 : Upper (D 5) (R 5) [18,68,136,34,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1355
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1356 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 305, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 140 42 276 33 72 161 289), lower := (rows 19 70 140 42 276 33 72 128 256), losses := [] }

theorem u1356 : Upper (D 5) (R 5) [18,68,136,34,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1356
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1357 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 19 70 140 42 276 33 96 137 265), lower := (rows 19 70 140 42 276 33 96 128 256), losses := [] }

theorem u1357 : Upper (D 5) (R 5) [18,68,136,34,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1357
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1358 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 140 42 280 33 65 164 292), lower := (rows 19 70 140 42 280 33 65 128 256), losses := [] }

theorem u1358 : Upper (D 5) (R 5) [18,68,136,34,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1358
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1359 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 70 140 42 280 33 68 161 289), lower := (rows 19 70 140 42 280 33 68 128 256), losses := [] }

theorem u1359 : Upper (D 5) (R 5) [18,68,136,34,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1359
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1360 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 19 70 140 42 280 33 96 133 261), lower := (rows 19 70 140 42 280 33 96 128 256), losses := [] }

theorem u1360 : Upper (D 5) (R 5) [18,68,136,34,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1360
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1361 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 140 42 304 33 65 140 268), lower := (rows 19 70 140 42 304 33 65 128 256), losses := [] }

theorem u1361 : Upper (D 5) (R 5) [18,68,136,34,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1361
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1362 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 70 140 42 304 33 68 137 265), lower := (rows 19 70 140 42 304 33 68 128 256), losses := [] }

theorem u1362 : Upper (D 5) (R 5) [18,68,136,34,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1362
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1363 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 305, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 140 42 304 33 72 133 261), lower := (rows 19 70 140 42 304 33 72 128 256), losses := [] }

theorem u1363 : Upper (D 5) (R 5) [18,68,136,34,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1363
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1364 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 140 44 25 34 65 416 288), lower := (rows 19 70 140 44 25 34 65 128 256), losses := [] }

theorem u1364 : Upper (D 5) (R 5) [18,68,136,36,9,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1364
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1365 : PairBound 9 := { available := 257, camps := [{ cop := 7, region := 110, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 140 44 25 34 96 385 257), lower := (rows 19 70 140 44 25 34 96 128 256), losses := [] }

theorem u1365 : Upper (D 5) (R 5) [18,68,136,36,9,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1365
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1366 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 19 70 140 44 25 34 320 161 289), lower := (rows 19 70 140 44 25 34 320 128 256), losses := [] }

theorem u1366 : Upper (D 5) (R 5) [18,68,136,36,9,2,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1366
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1367 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 83, targets := 32 }], pairs := [(0,5)], upper := (rows 19 70 140 44 25 288 65 162 290), lower := (rows 19 70 140 44 25 288 65 128 256), losses := [] }

theorem u1367 : Upper (D 5) (R 5) [18,68,136,36,9,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1367
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1368 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1)], upper := (rows 19 70 140 44 25 288 66 161 289), lower := (rows 19 70 140 44 25 288 66 128 256), losses := [] }

theorem u1368 : Upper (D 5) (R 5) [18,68,136,36,9,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1368
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1369 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 19 70 140 44 25 288 96 131 259), lower := (rows 19 70 140 44 25 288 96 128 256), losses := [] }

theorem u1369 : Upper (D 5) (R 5) [18,68,136,36,9,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1369
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1370 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 83, targets := 8 }], pairs := [(0,3)], upper := (rows 19 70 140 44 49 288 65 138 266), lower := (rows 19 70 140 44 49 288 65 128 256), losses := [] }

theorem u1370 : Upper (D 5) (R 5) [18,68,136,36,33,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1370
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1371 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1)], upper := (rows 19 70 140 44 49 288 66 137 265), lower := (rows 19 70 140 44 49 288 66 128 256), losses := [] }

theorem u1371 : Upper (D 5) (R 5) [18,68,136,36,33,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1371
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1372 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2)], upper := (rows 19 70 140 44 49 288 72 131 259), lower := (rows 19 70 140 44 49 288 72 128 256), losses := [] }

theorem u1372 : Upper (D 5) (R 5) [18,68,136,36,33,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1372
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1373 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 140, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 140 44 273 34 65 168 296), lower := (rows 19 70 140 44 273 34 65 128 256), losses := [] }

theorem u1373 : Upper (D 5) (R 5) [18,68,136,36,257,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1373
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1374 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 305, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 44 273 34 72 161 289), lower := (rows 19 70 140 44 273 34 72 128 256), losses := [] }

theorem u1374 : Upper (D 5) (R 5) [18,68,136,36,257,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1374
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1375 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 110, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 140 44 273 34 96 137 265), lower := (rows 19 70 140 44 273 34 96 128 256), losses := [] }

theorem u1375 : Upper (D 5) (R 5) [18,68,136,36,257,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1375
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1376 : PairBound 9 := { available := 34, camps := [], pairs := [(0,3),(3,1)], upper := (rows 19 70 140 44 280 33 65 162 290), lower := (rows 19 70 140 44 280 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 16 97 97 128 256), good := (rows 121 108 140 108 280 97 97 128 256) },{ target := 3, region := (rows 17 10 4 0 16 113 113 155 283), good := (rows 499 486 390 486 499 481 481 128 256) }] }

theorem u1376 : Upper (D 5) (R 5) [18,68,136,36,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1376
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1377 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 172, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 140 44 280 33 66 161 289), lower := (rows 19 70 140 44 280 33 66 128 256), losses := [] }

theorem u1377 : Upper (D 5) (R 5) [18,68,136,36,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1377
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1378 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 66, targets := 1 },{ cop := 3, region := 66, targets := 8 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 140 44 280 33 96 131 259), lower := (rows 19 70 140 44 280 33 96 128 256), losses := [] }

theorem u1378 : Upper (D 5) (R 5) [18,68,136,36,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1378
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1379 : Route 9 := (fun mask => (mask,id))

def c1379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1379 : Upper (D 5) (R 5) [18,68,136,36,264,2,1] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,264,2,1] 13 (by decide) (choices 1) [1,32] r1379 c1379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u72
  · exact u73

#print axioms u1379
end Delivery.IrregularNine14.P05
