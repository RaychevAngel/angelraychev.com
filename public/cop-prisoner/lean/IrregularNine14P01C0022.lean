import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0002
import IrregularNine14P01C0003

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1320 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 52, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 44 200 80 48 226 162 418), lower := (rows 275 7 44 200 80 48 64 128 256), losses := [] }

theorem u1320 : Upper (D 1) (R 1) [274,5,40,192,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1320
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1321 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 275 7 44 200 80 160 114 178 306), lower := (rows 275 7 44 200 80 160 64 128 256), losses := [] }

theorem u1321 : Upper (D 1) (R 1) [274,5,40,192,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1321
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1322 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 275 7 100 56 144 34 200 200 456), lower := (rows 275 7 100 56 144 34 64 128 256), losses := [] }

theorem u1322 : Upper (D 1) (R 1) [274,5,96,48,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1322
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1323 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 275 7 100 56 144 40 194 194 450), lower := (rows 275 7 100 56 144 40 64 128 256), losses := [] }

theorem u1323 : Upper (D 1) (R 1) [274,5,96,48,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1323
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1324 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 275 7 100 56 144 96 202 138 394), lower := (rows 275 7 100 56 144 96 64 128 256), losses := [] }

theorem u1324 : Upper (D 1) (R 1) [274,5,96,48,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1324
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1325 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 275 7 100 56 144 160 74 202 330), lower := (rows 275 7 100 56 144 160 64 128 256), losses := [] }

theorem u1325 : Upper (D 1) (R 1) [274,5,96,48,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1325
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1326 : PairBound 9 := { available := 88, camps := [{ cop := 5, region := 220, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 100 168 144 34 88 216 344), lower := (rows 275 7 100 168 144 34 64 128 256), losses := [] }

theorem u1326 : Upper (D 1) (R 1) [274,5,96,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1326
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1327 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 275 7 100 168 144 40 82 210 338), lower := (rows 275 7 100 168 144 40 64 128 256), losses := [] }

theorem u1327 : Upper (D 1) (R 1) [274,5,96,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1327
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1328 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 275 7 100 168 144 48 74 202 330), lower := (rows 275 7 100 168 144 48 64 128 256), losses := [] }

theorem u1328 : Upper (D 1) (R 1) [274,5,96,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1328
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1329 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 275 7 100 168 144 96 90 154 282), lower := (rows 275 7 100 168 144 96 64 128 256), losses := [] }

theorem u1329 : Upper (D 1) (R 1) [274,5,96,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1329
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1330 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 28 104 144 34 196 196 452), lower := (rows 275 35 28 104 144 34 64 128 256), losses := [] }

theorem u1330 : Upper (D 1) (R 1) [274,33,24,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1330
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1331 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 275 35 28 104 144 36 194 194 450), lower := (rows 275 35 28 104 144 36 64 128 256), losses := [] }

theorem u1331 : Upper (D 1) (R 1) [274,33,24,96,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1331
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1332 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 275 35 28 104 144 96 198 134 390), lower := (rows 275 35 28 104 144 96 64 128 256), losses := [] }

theorem u1332 : Upper (D 1) (R 1) [274,33,24,96,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1332
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1333 : PairBound 9 := { available := 70, camps := [], pairs := [(2,1)], upper := (rows 275 35 28 104 144 160 70 198 326), lower := (rows 275 35 28 104 144 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 176 176 64 128 256), good := (rows 305 49 60 124 176 176 64 176 256) }] }

theorem u1333 : Upper (D 1) (R 1) [274,33,24,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1333
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1334 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 44 88 144 34 196 196 452), lower := (rows 275 35 44 88 144 34 64 128 256), losses := [] }

theorem u1334 : Upper (D 1) (R 1) [274,33,40,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1334
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1335 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 275 35 44 88 144 36 194 194 450), lower := (rows 275 35 44 88 144 36 64 128 256), losses := [] }

theorem u1335 : Upper (D 1) (R 1) [274,33,40,80,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1335
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1336 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 36, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 44 88 144 96 198 134 390), lower := (rows 275 35 44 88 144 96 64 128 256), losses := [] }

theorem u1336 : Upper (D 1) (R 1) [274,33,40,80,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1336
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1337 : PairBound 9 := { available := 70, camps := [], pairs := [(2,1)], upper := (rows 275 35 44 88 144 160 70 198 326), lower := (rows 275 35 44 88 144 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 176 176 64 128 256), good := (rows 305 49 60 124 176 176 64 176 256) }] }

theorem u1337 : Upper (D 1) (R 1) [274,33,40,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1337
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1338 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 44 200 80 34 212 148 404), lower := (rows 275 35 44 200 80 34 64 128 256), losses := [] }

theorem u1338 : Upper (D 1) (R 1) [274,33,40,192,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1338
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1339 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 275 35 44 200 80 36 210 146 402), lower := (rows 275 35 44 200 80 36 64 128 256), losses := [] }

theorem u1339 : Upper (D 1) (R 1) [274,33,40,192,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1339
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1340 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 275 35 44 200 80 48 198 134 390), lower := (rows 275 35 44 200 80 48 64 128 256), losses := [] }

theorem u1340 : Upper (D 1) (R 1) [274,33,40,192,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1340
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1341 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 275 35 44 200 80 160 86 150 278), lower := (rows 275 35 44 200 80 160 64 128 256), losses := [] }

theorem u1341 : Upper (D 1) (R 1) [274,33,40,192,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1341
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1342 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 275 35 52 76 80 34 200 136 392), lower := (rows 275 35 52 76 80 34 64 128 256), losses := [] }

theorem u1342 : Upper (D 1) (R 1) [274,33,48,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1342
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1343 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 275 35 52 76 80 40 194 130 386), lower := (rows 275 35 52 76 80 40 64 128 256), losses := [] }

theorem u1343 : Upper (D 1) (R 1) [274,33,48,68,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1343
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1344 : Route 9 := (fun mask => (mask,id))

def c1344 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1344 : Upper (D 1) (R 1) [274,33,48,68,64,128] 13 := by
  apply FastRouting.sound _ _ [274,33,48,68,64,128] 13 (by decide) (choices 1) [2,8,128] r1344 c1344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u167
  · exact u168
  · exact u169

def b1345 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 275 35 52 76 144 34 200 200 456), lower := (rows 275 35 52 76 144 34 64 128 256), losses := [] }

theorem u1345 : Upper (D 1) (R 1) [274,33,48,68,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1345
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1346 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 275 35 52 76 144 40 194 194 450), lower := (rows 275 35 52 76 144 40 64 128 256), losses := [] }

theorem u1346 : Upper (D 1) (R 1) [274,33,48,68,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1346
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1347 : Route 9 := (fun mask => (mask,id))

def c1347 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1347 : Upper (D 1) (R 1) [274,33,48,68,128,64] 13 := by
  apply FastRouting.sound _ _ [274,33,48,68,128,64] 13 (by decide) (choices 1) [2,8,128] r1347 c1347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u170
  · exact u171
  · exact u172

def b1348 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 275 35 52 76 144 160 74 202 330), lower := (rows 275 35 52 76 144 160 64 128 256), losses := [] }

theorem u1348 : Upper (D 1) (R 1) [274,33,48,68,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1348
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1349 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 275 35 52 200 80 34 204 140 396), lower := (rows 275 35 52 200 80 34 64 128 256), losses := [] }

theorem u1349 : Upper (D 1) (R 1) [274,33,48,192,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1349
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1350 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 275 35 52 200 80 36 202 138 394), lower := (rows 275 35 52 200 80 36 64 128 256), losses := [] }

theorem u1350 : Upper (D 1) (R 1) [274,33,48,192,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1350
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1351 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 275 35 52 200 80 40 198 134 390), lower := (rows 275 35 52 200 80 40 64 128 256), losses := [] }

theorem u1351 : Upper (D 1) (R 1) [274,33,48,192,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1351
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1352 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 52, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 52 200 80 160 78 142 270), lower := (rows 275 35 52 200 80 160 64 128 256), losses := [] }

theorem u1352 : Upper (D 1) (R 1) [274,33,48,192,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1352
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1353 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 76 152 80 34 228 164 420), lower := (rows 275 35 76 152 80 34 64 128 256), losses := [] }

theorem u1353 : Upper (D 1) (R 1) [274,33,72,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1353
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1354 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 275 35 76 152 80 36 226 162 418), lower := (rows 275 35 76 152 80 36 64 128 256), losses := [] }

theorem u1354 : Upper (D 1) (R 1) [274,33,72,144,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1354
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1355 : Route 9 := (fun mask => (mask,id))

def c1355 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1355 : Upper (D 1) (R 1) [274,33,72,144,64,128] 13 := by
  apply FastRouting.sound _ _ [274,33,72,144,64,128] 13 (by decide) (choices 1) [2,4,32] r1355 c1355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u173
  · exact u174
  · exact u175

def b1356 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 76 168 80 34 212 148 404), lower := (rows 275 35 76 168 80 34 64 128 256), losses := [] }

theorem u1356 : Upper (D 1) (R 1) [274,33,72,160,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1356
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1357 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 275 35 76 168 80 36 210 146 402), lower := (rows 275 35 76 168 80 36 64 128 256), losses := [] }

theorem u1357 : Upper (D 1) (R 1) [274,33,72,160,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1357
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1358 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 275 35 76 168 80 48 198 134 390), lower := (rows 275 35 76 168 80 48 64 128 256), losses := [] }

theorem u1358 : Upper (D 1) (R 1) [274,33,72,160,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1358
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1359 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 275 35 76 168 80 160 86 150 278), lower := (rows 275 35 76 168 80 160 64 128 256), losses := [] }

theorem u1359 : Upper (D 1) (R 1) [274,33,72,160,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1359
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1360 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 76 168 144 34 84 212 340), lower := (rows 275 35 76 168 144 34 64 128 256), losses := [] }

theorem u1360 : Upper (D 1) (R 1) [274,33,72,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1360
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1361 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 275 35 76 168 144 36 82 210 338), lower := (rows 275 35 76 168 144 36 64 128 256), losses := [] }

theorem u1361 : Upper (D 1) (R 1) [274,33,72,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1361
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1362 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 275 35 76 168 144 48 70 198 326), lower := (rows 275 35 76 168 144 48 64 128 256), losses := [] }

theorem u1362 : Upper (D 1) (R 1) [274,33,72,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1362
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1363 : Route 9 := (fun mask => (mask,id))

def c1363 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1363 : Upper (D 1) (R 1) [274,33,72,160,128,64] 13 := by
  apply FastRouting.sound _ _ [274,33,72,160,128,64] 13 (by decide) (choices 1) [2,4,16] r1363 c1363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u176
  · exact u177
  · exact u178

def b1364 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 84 104 144 34 204 140 396), lower := (rows 275 35 84 104 144 34 64 128 256), losses := [] }

theorem u1364 : Upper (D 1) (R 1) [274,33,80,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1364
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1365 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 275 35 84 104 144 36 202 138 394), lower := (rows 275 35 84 104 144 36 64 128 256), losses := [] }

theorem u1365 : Upper (D 1) (R 1) [274,33,80,96,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1365
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1366 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 275 35 84 104 144 40 198 134 390), lower := (rows 275 35 84 104 144 40 64 128 256), losses := [] }

theorem u1366 : Upper (D 1) (R 1) [274,33,80,96,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1366
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1367 : PairBound 9 := { available := 14, camps := [], pairs := [(2,1)], upper := (rows 275 35 84 104 144 160 78 142 270), lower := (rows 275 35 84 104 144 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 12 176 176 64 128 256), good := (rows 305 49 124 124 176 176 64 176 256) }] }

theorem u1367 : Upper (D 1) (R 1) [274,33,80,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1367
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1368 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 84 168 144 34 76 204 332), lower := (rows 275 35 84 168 144 34 64 128 256), losses := [] }

theorem u1368 : Upper (D 1) (R 1) [274,33,80,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1368
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1369 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 275 35 84 168 144 36 74 202 330), lower := (rows 275 35 84 168 144 36 64 128 256), losses := [] }

theorem u1369 : Upper (D 1) (R 1) [274,33,80,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1369
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1370 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 275 35 84 168 144 40 70 198 326), lower := (rows 275 35 84 168 144 40 64 128 256), losses := [] }

theorem u1370 : Upper (D 1) (R 1) [274,33,80,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1370
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1371 : Route 9 := (fun mask => (mask,id))

def c1371 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1371 : Upper (D 1) (R 1) [274,33,80,160,128,64] 13 := by
  apply FastRouting.sound _ _ [274,33,80,160,128,64] 13 (by decide) (choices 1) [2,4,8] r1371 c1371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u179
  · exact u180
  · exact u181

def b1372 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 100 200 144 34 92 156 284), lower := (rows 275 35 100 200 144 34 64 128 256), losses := [] }

theorem u1372 : Upper (D 1) (R 1) [274,33,96,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1372
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1373 : PairBound 9 := { available := 26, camps := [], pairs := [], upper := (rows 275 35 100 200 144 36 90 154 282), lower := (rows 275 35 100 200 144 36 64 128 256), losses := [] }

theorem u1373 : Upper (D 1) (R 1) [274,33,96,192,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1373
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1374 : PairBound 9 := { available := 22, camps := [], pairs := [], upper := (rows 275 35 100 200 144 40 86 150 278), lower := (rows 275 35 100 200 144 40 64 128 256), losses := [] }

theorem u1374 : Upper (D 1) (R 1) [274,33,96,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1374
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1375 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 275 35 100 200 144 48 78 142 270), lower := (rows 275 35 100 200 144 48 64 128 256), losses := [] }

theorem u1375 : Upper (D 1) (R 1) [274,33,96,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1375
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1376 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 13 74 144 48 224 224 480), lower := (rows 275 38 13 74 144 48 64 128 256), losses := [] }

theorem u1376 : Upper (D 1) (R 1) [274,36,9,66,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1376
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1377 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 275 38 13 74 144 96 240 176 432), lower := (rows 275 38 13 74 144 96 64 128 256), losses := [] }

theorem u1377 : Upper (D 1) (R 1) [274,36,9,66,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1377
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1378 : Route 9 := (fun mask => (mask,id))

def c1378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1378 : Upper (D 1) (R 1) [274,36,9,66,128,128] 13 := by
  apply FastRouting.sound _ _ [274,36,9,66,128,128] 13 (by decide) (choices 1) [16,32] r1378 c1378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u182
  · exact u183

def b1379 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 69 56 144 34 200 200 456), lower := (rows 275 38 69 56 144 34 64 128 256), losses := [] }

theorem u1379 : Upper (D 1) (R 1) [274,36,65,48,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1379
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1379
end Delivery.IrregularNine14.P01
