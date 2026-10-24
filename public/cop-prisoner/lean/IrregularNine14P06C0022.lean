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

def b1320 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 0, region := 328, targets := 32 }], pairs := [(3,5),(4,0),(4,2)], upper := (rows 7 42 148 328 112 33 66 133 261), lower := (rows 7 42 148 328 112 33 66 128 256), losses := [] }

theorem u1320 : Upper (D 6) (R 6) [6,40,144,320,96,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1320
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1321 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 112, targets := 2 },{ cop := 0, region := 328, targets := 32 }], pairs := [(3,5),(4,0),(4,1)], upper := (rows 7 42 148 328 112 33 68 131 259), lower := (rows 7 42 148 328 112 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 48 32 69 128 256), good := (rows 70 58 212 328 112 112 68 128 256) }] }

theorem u1321 : Upper (D 6) (R 6) [6,40,144,320,96,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1321
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1322 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 328, targets := 36 },{ cop := 0, region := 112, targets := 2 }], pairs := [(3,2),(3,5),(4,1)], upper := (rows 7 42 148 328 112 36 65 131 259), lower := (rows 7 42 148 328 112 36 65 128 256), losses := [] }

theorem u1322 : Upper (D 6) (R 6) [6,40,144,320,96,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1322
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1323 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 328, targets := 36 },{ cop := 1, region := 80, targets := 1 }], pairs := [(3,2),(3,5),(4,0)], upper := (rows 7 42 148 328 112 36 66 129 257), lower := (rows 7 42 148 328 112 36 66 128 256), losses := [] }

theorem u1323 : Upper (D 6) (R 6) [6,40,144,320,96,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1323
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1324 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 42 164 88 276 33 65 194 322), lower := (rows 7 42 164 88 276 33 65 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 97 97 139 267), good := (rows 483 490 224 506 272 481 481 128 256) }] }

theorem u1324 : Upper (D 6) (R 6) [6,40,160,80,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1324
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1325 : Route 9 := (fun mask => (mask,id))

def c1325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1325 : Upper (D 6) (R 6) [6,40,160,80,260,1,2] 13 := by
  apply FastRouting.sound _ _ [6,40,160,80,260,1,2] 13 (by decide) (choices 1) [1,64] r1325 c1325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u74
  · exact u75

def b1326 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 98, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 42 164 265 81 96 66 148 276), lower := (rows 7 42 164 265 81 96 66 128 256), losses := [] }

theorem u1326 : Upper (D 6) (R 6) [6,40,160,257,65,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1326
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1327 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 4, region := 298, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 42 164 265 81 96 68 146 274), lower := (rows 7 42 164 265 81 96 68 128 256), losses := [] }

theorem u1327 : Upper (D 6) (R 6) [6,40,160,257,65,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1327
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1328 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 164 265 81 96 80 134 262), lower := (rows 7 42 164 265 81 96 80 128 256), losses := [] }

theorem u1328 : Upper (D 6) (R 6) [6,40,160,257,65,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1328
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1329 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 98, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 42 164 265 82 96 65 148 276), lower := (rows 7 42 164 265 82 96 65 128 256), losses := [] }

theorem u1329 : Upper (D 6) (R 6) [6,40,160,257,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1329
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1330 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 164 265 82 96 68 145 273), lower := (rows 7 42 164 265 82 96 68 128 256), losses := [] }

theorem u1330 : Upper (D 6) (R 6) [6,40,160,257,66,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1330
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1331 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 114, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 164 265 82 96 80 133 261), lower := (rows 7 42 164 265 82 96 80 128 256), losses := [] }

theorem u1331 : Upper (D 6) (R 6) [6,40,160,257,66,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1331
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1332 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 42 164 265 84 96 65 146 274), lower := (rows 7 42 164 265 84 96 65 128 256), losses := [] }

theorem u1332 : Upper (D 6) (R 6) [6,40,160,257,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1332
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1333 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 42 164 265 84 96 66 145 273), lower := (rows 7 42 164 265 84 96 66 128 256), losses := [] }

theorem u1333 : Upper (D 6) (R 6) [6,40,160,257,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1333
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1334 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 164 265 84 96 80 131 259), lower := (rows 7 42 164 265 84 96 80 128 256), losses := [] }

theorem u1334 : Upper (D 6) (R 6) [6,40,160,257,68,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1334
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1335 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 42 164 280 84 33 65 194 322), lower := (rows 7 42 164 280 84 33 65 128 256), losses := [] }

theorem u1335 : Upper (D 6) (R 6) [6,40,160,272,68,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1335
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1336 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 80, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 7 42 164 280 84 33 66 193 321), lower := (rows 7 42 164 280 84 33 66 128 256), losses := [] }

theorem u1336 : Upper (D 6) (R 6) [6,40,160,272,68,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1336
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1337 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 4, region := 164, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 42 164 328 81 33 66 148 276), lower := (rows 7 42 164 328 81 33 66 128 256), losses := [] }

theorem u1337 : Upper (D 6) (R 6) [6,40,160,320,65,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1337
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1338 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 4, region := 298, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 42 164 328 81 33 68 146 274), lower := (rows 7 42 164 328 81 33 68 128 256), losses := [] }

theorem u1338 : Upper (D 6) (R 6) [6,40,160,320,65,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1338
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1339 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 164 328 81 33 80 134 262), lower := (rows 7 42 164 328 81 33 80 128 256), losses := [] }

theorem u1339 : Upper (D 6) (R 6) [6,40,160,320,65,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1339
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1340 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 42 164 328 84 33 65 146 274), lower := (rows 7 42 164 328 84 33 65 128 256), losses := [] }

theorem u1340 : Upper (D 6) (R 6) [6,40,160,320,68,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1340
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1341 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 80, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 7 42 164 328 84 33 66 145 273), lower := (rows 7 42 164 328 84 33 66 128 256), losses := [] }

theorem u1341 : Upper (D 6) (R 6) [6,40,160,320,68,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1341
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1342 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 42 164 328 84 33 80 131 259), lower := (rows 7 42 164 328 84 33 80 128 256), losses := [] }

theorem u1342 : Upper (D 6) (R 6) [6,40,160,320,68,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1342
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1343 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 3 },{ cop := 3, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 7 42 196 25 274 96 65 164 292), lower := (rows 7 42 196 25 274 96 65 128 256), losses := [] }

theorem u1343 : Upper (D 6) (R 6) [6,40,192,17,258,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1343
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1344 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 68, targets := 3 },{ cop := 7, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 42 196 25 274 96 68 161 289), lower := (rows 7 42 196 25 274 96 68 128 256), losses := [] }

theorem u1344 : Upper (D 6) (R 6) [6,40,192,17,258,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1344
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1345 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 280, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 196 25 274 96 96 133 261), lower := (rows 7 42 196 25 274 96 96 128 256), losses := [] }

theorem u1345 : Upper (D 6) (R 6) [6,40,192,17,258,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1345
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1346 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 196 25 276 96 65 162 290), lower := (rows 7 42 196 25 276 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 8 81 100 64 131 259), good := (rows 438 426 244 408 308 116 500 128 256) }] }

theorem u1346 : Upper (D 6) (R 6) [6,40,192,17,260,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1346
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1347 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 98, targets := 1 },{ cop := 3, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(3,1)], upper := (rows 7 42 196 25 276 96 66 161 289), lower := (rows 7 42 196 25 276 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 100 64 129 257), good := (rows 445 40 228 409 308 96 96 128 256) }] }

theorem u1347 : Upper (D 6) (R 6) [6,40,192,17,260,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1347
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1348 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 280, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 196 25 276 96 96 131 259), lower := (rows 7 42 196 25 276 96 96 128 256), losses := [] }

theorem u1348 : Upper (D 6) (R 6) [6,40,192,17,260,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1348
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1349 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 3, region := 98, targets := 4 }], pairs := [(0,5),(1,2),(2,5)], upper := (rows 7 42 196 25 304 96 65 134 262), lower := (rows 7 42 196 25 304 96 65 128 256), losses := [] }

theorem u1349 : Upper (D 6) (R 6) [6,40,192,17,288,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1349
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1350 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 42 196 25 304 96 66 133 261), lower := (rows 7 42 196 25 304 96 66 128 256), losses := [] }

theorem u1350 : Upper (D 6) (R 6) [6,40,192,17,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1350
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1351 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 7, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(2,5)], upper := (rows 7 42 196 25 304 96 68 131 259), lower := (rows 7 42 196 25 304 96 68 128 256), losses := [] }

theorem u1351 : Upper (D 6) (R 6) [6,40,192,17,288,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1351
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1352 : PairBound 9 := { available := 34, camps := [], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 42 196 25 336 36 65 162 290), lower := (rows 7 42 196 25 336 36 65 128 256), losses := [{ target := 0, region := (rows 0 10 68 8 80 117 64 139 267), good := (rows 422 426 244 442 372 36 500 128 256) }] }

theorem u1352 : Upper (D 6) (R 6) [6,40,192,17,320,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1352
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1353 : Route 9 := (fun mask => (mask,id))

def c1353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1353 : Upper (D 6) (R 6) [6,40,192,17,320,4,2] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,320,4,2] 13 (by decide) (choices 1) [1,32] r1353 c1353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u76
  · exact u77

def b1354 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 7 42 196 25 336 36 96 131 259), lower := (rows 7 42 196 25 336 36 96 128 256), losses := [{ target := 0, region := (rows 0 10 132 8 16 165 239 128 256), good := (rows 102 106 228 122 336 100 96 228 256) }] }

theorem u1354 : Upper (D 6) (R 6) [6,40,192,17,320,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1354
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1355 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 106, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 196 26 273 96 65 164 292), lower := (rows 7 42 196 26 273 96 65 128 256), losses := [] }

theorem u1355 : Upper (D 6) (R 6) [6,40,192,18,257,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1355
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1356 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 7, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 42 196 26 273 96 68 161 289), lower := (rows 7 42 196 26 273 96 68 128 256), losses := [] }

theorem u1356 : Upper (D 6) (R 6) [6,40,192,18,257,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1356
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1357 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 280, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 196 26 273 96 96 133 261), lower := (rows 7 42 196 26 273 96 96 128 256), losses := [] }

theorem u1357 : Upper (D 6) (R 6) [6,40,192,18,257,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1357
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1358 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 196 26 336 33 65 164 292), lower := (rows 7 42 196 26 336 33 65 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 97 97 128 256), good := (rows 99 106 224 26 378 97 97 128 256) }] }

theorem u1358 : Upper (D 6) (R 6) [6,40,192,18,320,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1358
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1359 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 42 196 26 336 33 68 161 289), lower := (rows 7 42 196 26 336 33 68 128 256), losses := [] }

theorem u1359 : Upper (D 6) (R 6) [6,40,192,18,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1359
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1360 : Route 9 := (fun mask => (mask,id))

def c1360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1360 : Upper (D 6) (R 6) [6,40,192,18,320,1,32] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,320,1,32] 13 (by decide) (choices 1) [1,4] r1360 c1360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u78
  · exact u79

def r1361 : Route 9 := (fun mask => (mask,id))

def c1361 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1361 : Upper (D 6) (R 6) [6,40,192,18,320,4,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,320,4,1] 13 (by decide) (choices 1) [1,32] r1361 c1361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u80
  · exact u81

def b1362 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 42 196 26 336 36 96 129 257), lower := (rows 7 42 196 26 336 36 96 128 256), losses := [] }

theorem u1362 : Upper (D 6) (R 6) [6,40,192,18,320,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1362
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1363 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 72, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 42 196 88 273 36 65 162 290), lower := (rows 7 42 196 88 273 36 65 128 256), losses := [] }

theorem u1363 : Upper (D 6) (R 6) [6,40,192,80,257,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1363
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1364 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 66 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 7 42 196 88 273 36 66 161 289), lower := (rows 7 42 196 88 273 36 66 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 91 128 256), good := (rows 102 106 228 90 378 36 66 128 256) }] }

theorem u1364 : Upper (D 6) (R 6) [6,40,192,80,257,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1364
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1365 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 272, targets := 36 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 7 42 196 88 273 36 96 131 259), lower := (rows 7 42 196 88 273 36 96 128 256), losses := [] }

theorem u1365 : Upper (D 6) (R 6) [6,40,192,80,257,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1365
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1366 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 304, targets := 64 }], pairs := [(1,2),(2,1),(4,6)], upper := (rows 7 42 196 88 274 33 65 164 292), lower := (rows 7 42 196 88 274 33 65 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 97 97 128 256), good := (rows 99 106 224 122 274 97 97 128 256) }] }

theorem u1366 : Upper (D 6) (R 6) [6,40,192,80,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1366
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1367 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 42 196 88 274 33 68 161 289), lower := (rows 7 42 196 88 274 33 68 128 256), losses := [] }

theorem u1367 : Upper (D 6) (R 6) [6,40,192,80,258,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1367
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1368 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 272, targets := 32 },{ cop := 0, region := 272, targets := 64 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 7 42 196 88 274 33 96 133 261), lower := (rows 7 42 196 88 274 33 96 128 256), losses := [] }

theorem u1368 : Upper (D 6) (R 6) [6,40,192,80,258,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1368
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1369 : Route 9 := (fun mask => (mask,id))

def c1369 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1369 : Upper (D 6) (R 6) [6,40,192,80,258,4,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,258,4,1] 13 (by decide) (choices 1) [1,32] r1369 c1369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u82
  · exact u83

def b1370 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 36 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 7 42 196 88 274 36 96 129 257), lower := (rows 7 42 196 88 274 36 96 128 256), losses := [] }

theorem u1370 : Upper (D 6) (R 6) [6,40,192,80,258,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1370
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1371 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(3,0),(4,0),(4,6)], upper := (rows 7 42 196 88 276 33 65 162 290), lower := (rows 7 42 196 88 276 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 17 32 64 130 258), good := (rows 406 426 204 88 276 48 88 128 256) }] }

theorem u1371 : Upper (D 6) (R 6) [6,40,192,80,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1371
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1372 : Route 9 := (fun mask => (mask,id))

def c1372 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1372 : Upper (D 6) (R 6) [6,40,192,80,260,1,2] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,260,1,2] 13 (by decide) (choices 1) [1,32] r1372 c1372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u84
  · exact u85

def r1373 : Route 9 := (fun mask => (mask,id))

def c1373 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1373 : Upper (D 6) (R 6) [6,40,192,80,260,1,32] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,260,1,32] 13 (by decide) (choices 1) [1,2] r1373 c1373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u86
  · exact u87

def b1374 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 114, targets := 4 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 7 42 196 265 49 96 66 148 276), lower := (rows 7 42 196 265 49 96 66 128 256), losses := [] }

theorem u1374 : Upper (D 6) (R 6) [6,40,192,257,33,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1374
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1375 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 266, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 42 196 265 49 96 68 146 274), lower := (rows 7 42 196 265 49 96 68 128 256), losses := [] }

theorem u1375 : Upper (D 6) (R 6) [6,40,192,257,33,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1375
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1376 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 42 196 265 49 96 80 134 262), lower := (rows 7 42 196 265 49 96 80 128 256), losses := [] }

theorem u1376 : Upper (D 6) (R 6) [6,40,192,257,33,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1376
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1377 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 114, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 42 196 265 81 48 66 164 292), lower := (rows 7 42 196 265 81 48 66 128 256), losses := [] }

theorem u1377 : Upper (D 6) (R 6) [6,40,192,257,65,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1377
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1378 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 298, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 42 196 265 81 48 68 162 290), lower := (rows 7 42 196 265 81 48 68 128 256), losses := [] }

theorem u1378 : Upper (D 6) (R 6) [6,40,192,257,65,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1378
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1379 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 42 196 265 81 48 96 134 262), lower := (rows 7 42 196 265 81 48 96 128 256), losses := [] }

theorem u1379 : Upper (D 6) (R 6) [6,40,192,257,65,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1379
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1379
end Delivery.IrregularNine14.P06
