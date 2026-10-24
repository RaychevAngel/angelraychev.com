import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0006

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1320 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 67 196 268 24 177 241 177 433), lower := (rows 51 67 196 268 24 32 64 128 256), losses := [] }

theorem u1320 : Upper (D 0) (R 0) [50,65,192,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1320
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1321 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 196 268 48 185 217 153 409), lower := (rows 51 67 196 268 48 32 64 128 256), losses := [] }

theorem u1321 : Upper (D 0) (R 0) [50,65,192,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1321
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1322_1 : Upper (D 0) (R 0) [50,65,192,260,128,1] 13 :=
  permutation_upper _ _ _ [50,65,192,260,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u362

theorem m1322_8 : Upper (D 0) (R 0) [50,65,192,260,128,8] 13 :=
  permutation_upper _ _ _ [50,65,192,260,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u363

theorem m1322_16 : Upper (D 0) (R 0) [50,65,192,260,128,16] 13 :=
  permutation_upper _ _ _ [50,65,192,260,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u364

def r1322 : Route 9 := (fun mask => (mask,id))

def c1322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1322 : Upper (D 0) (R 0) [50,65,192,260,128] 13 := by
  apply FastRouting.sound _ _ [50,65,192,260,128] 13 (by decide) (choices 1) [1,8,16] r1322 c1322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1322_1
  · exact m1322_8
  · exact m1322_16

def b1323 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 196 280 17 172 236 172 428), lower := (rows 51 67 196 280 17 32 64 128 256), losses := [] }

theorem u1323 : Upper (D 0) (R 0) [50,65,192,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1323
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1324 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 51 67 196 280 20 169 233 169 425), lower := (rows 51 67 196 280 20 32 64 128 256), losses := [] }

theorem u1324 : Upper (D 0) (R 0) [50,65,192,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1324
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1325 : PairBound 9 := { available := 165, camps := [], pairs := [], upper := (rows 51 67 196 280 24 165 229 165 421), lower := (rows 51 67 196 280 24 32 64 128 256), losses := [] }

theorem u1325 : Upper (D 0) (R 0) [50,65,192,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1325
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1326 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 196 280 48 173 205 141 397), lower := (rows 51 67 196 280 48 32 64 128 256), losses := [] }

theorem u1326 : Upper (D 0) (R 0) [50,65,192,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1326
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1327 : Route 9 := (fun mask => (mask,id))

def c1327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1327 : Upper (D 0) (R 0) [50,65,192,272,128] 13 := by
  apply FastRouting.sound _ _ [50,65,192,272,128] 13 (by decide) (choices 1) [1,4,8] r1327 c1327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u365
  · exact u366
  · exact u367

def b1328 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 196 392 17 60 124 188 316), lower := (rows 51 67 196 392 17 32 64 128 256), losses := [] }

theorem u1328 : Upper (D 0) (R 0) [50,65,192,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1328
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1329 : PairBound 9 := { available := 57, camps := [], pairs := [], upper := (rows 51 67 196 392 20 57 121 185 313), lower := (rows 51 67 196 392 20 32 64 128 256), losses := [] }

theorem u1329 : Upper (D 0) (R 0) [50,65,192,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1329
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1330 : PairBound 9 := { available := 53, camps := [], pairs := [], upper := (rows 51 67 196 392 24 53 117 181 309), lower := (rows 51 67 196 392 24 32 64 128 256), losses := [] }

theorem u1330 : Upper (D 0) (R 0) [50,65,192,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1330
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1331 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 196 392 48 61 93 157 285), lower := (rows 51 67 196 392 48 32 64 128 256), losses := [] }

theorem u1331 : Upper (D 0) (R 0) [50,65,192,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1331
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1332 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 51 70 13 392 17 240 240 240 496), lower := (rows 51 70 13 392 17 32 64 128 256), losses := [] }

theorem u1332 : Upper (D 0) (R 0) [50,68,9,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1332
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1333 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 13 392 48 241 209 209 465), lower := (rows 51 70 13 392 48 32 64 128 256), losses := [] }

theorem u1333 : Upper (D 0) (R 0) [50,68,9,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1333
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1334 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 13 392 80 177 241 177 433), lower := (rows 51 70 13 392 80 32 64 128 256), losses := [] }

theorem u1334 : Upper (D 0) (R 0) [50,68,9,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1334
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1335 : PairBound 9 := { available := 113, camps := [], pairs := [(1,7)], upper := (rows 51 70 13 392 144 113 113 241 369), lower := (rows 51 70 13 392 144 32 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 33 65 0 257), good := (rows 371 70 367 264 16 32 64 0 256) }] }

theorem u1335 : Upper (D 0) (R 0) [50,68,9,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1335
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1336 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 51 70 133 88 17 424 488 424 424), lower := (rows 51 70 133 88 17 32 64 128 256), losses := [] }

theorem u1336 : Upper (D 0) (R 0) [50,68,129,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1336
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1337 : PairBound 9 := { available := 417, camps := [], pairs := [], upper := (rows 51 70 133 88 24 417 481 417 417), lower := (rows 51 70 133 88 24 32 64 128 256), losses := [] }

theorem u1337 : Upper (D 0) (R 0) [50,68,129,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1337
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1338 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 133 88 48 425 457 393 393), lower := (rows 51 70 133 88 48 32 64 128 256), losses := [] }

theorem u1338 : Upper (D 0) (R 0) [50,68,129,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1338
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1339 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 133 88 144 297 361 425 297), lower := (rows 51 70 133 88 144 32 64 128 256), losses := [] }

theorem u1339 : Upper (D 0) (R 0) [50,68,129,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1339
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1340 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 51 70 133 88 272 169 233 169 425), lower := (rows 51 70 133 88 272 32 64 128 256), losses := [] }

theorem u1340 : Upper (D 0) (R 0) [50,68,129,80,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1340
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1341 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 133 152 17 360 360 488 360), lower := (rows 51 70 133 152 17 32 64 128 256), losses := [] }

theorem u1341 : Upper (D 0) (R 0) [50,68,129,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1341
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1342 : PairBound 9 := { available := 353, camps := [], pairs := [], upper := (rows 51 70 133 152 24 353 353 481 353), lower := (rows 51 70 133 152 24 32 64 128 256), losses := [] }

theorem u1342 : Upper (D 0) (R 0) [50,68,129,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1342
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1343 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 133 152 48 361 329 457 329), lower := (rows 51 70 133 152 48 32 64 128 256), losses := [] }

theorem u1343 : Upper (D 0) (R 0) [50,68,129,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1343
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1344 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 133 152 80 297 361 425 297), lower := (rows 51 70 133 152 80 32 64 128 256), losses := [] }

theorem u1344 : Upper (D 0) (R 0) [50,68,129,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1344
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1345 : PairBound 9 := { available := 105, camps := [], pairs := [], upper := (rows 51 70 133 152 272 105 105 233 361), lower := (rows 51 70 133 152 272 32 64 128 256), losses := [] }

theorem u1345 : Upper (D 0) (R 0) [50,68,129,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1345
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1346 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 51 70 133 200 17 312 376 440 312), lower := (rows 51 70 133 200 17 32 64 128 256), losses := [] }

theorem u1346 : Upper (D 0) (R 0) [50,68,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1346
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1347 : PairBound 9 := { available := 305, camps := [], pairs := [], upper := (rows 51 70 133 200 24 305 369 433 305), lower := (rows 51 70 133 200 24 32 64 128 256), losses := [] }

theorem u1347 : Upper (D 0) (R 0) [50,68,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1347
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1348 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 133 200 48 313 345 409 281), lower := (rows 51 70 133 200 48 32 64 128 256), losses := [] }

theorem u1348 : Upper (D 0) (R 0) [50,68,129,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1348
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1349 : PairBound 9 := { available := 57, camps := [], pairs := [], upper := (rows 51 70 133 200 272 57 121 185 313), lower := (rows 51 70 133 200 272 32 64 128 256), losses := [] }

theorem u1349 : Upper (D 0) (R 0) [50,68,129,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1349
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1350 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 70 133 265 24 240 240 240 496), lower := (rows 51 70 133 265 24 32 64 128 256), losses := [] }

theorem u1350 : Upper (D 0) (R 0) [50,68,129,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1350
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1351 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 133 265 48 248 216 216 472), lower := (rows 51 70 133 265 48 32 64 128 256), losses := [] }

theorem u1351 : Upper (D 0) (R 0) [50,68,129,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1351
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1352 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 133 265 80 184 248 184 440), lower := (rows 51 70 133 265 80 32 64 128 256), losses := [] }

theorem u1352 : Upper (D 0) (R 0) [50,68,129,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1352
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1353 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 133 265 144 120 120 248 376), lower := (rows 51 70 133 265 144 32 64 128 256), losses := [] }

theorem u1353 : Upper (D 0) (R 0) [50,68,129,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1353
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1354 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 51 70 133 280 17 232 232 232 488), lower := (rows 51 70 133 280 17 32 64 128 256), losses := [] }

theorem u1354 : Upper (D 0) (R 0) [50,68,129,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1354
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1355 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 70 133 280 24 225 225 225 481), lower := (rows 51 70 133 280 24 32 64 128 256), losses := [] }

theorem u1355 : Upper (D 0) (R 0) [50,68,129,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1355
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1356 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 133 280 48 233 201 201 457), lower := (rows 51 70 133 280 48 32 64 128 256), losses := [] }

theorem u1356 : Upper (D 0) (R 0) [50,68,129,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1356
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1357 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 133 280 80 169 233 169 425), lower := (rows 51 70 133 280 80 32 64 128 256), losses := [] }

theorem u1357 : Upper (D 0) (R 0) [50,68,129,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1357
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1358 : PairBound 9 := { available := 105, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 133 280 144 105 105 233 361), lower := (rows 51 70 133 280 144 32 64 128 256), losses := [] }

theorem u1358 : Upper (D 0) (R 0) [50,68,129,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1358
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1359 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 51 70 133 328 17 184 248 184 440), lower := (rows 51 70 133 328 17 32 64 128 256), losses := [] }

theorem u1359 : Upper (D 0) (R 0) [50,68,129,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1359
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1360 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 70 133 328 24 177 241 177 433), lower := (rows 51 70 133 328 24 32 64 128 256), losses := [] }

theorem u1360 : Upper (D 0) (R 0) [50,68,129,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1360
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1361 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 133 328 48 185 217 153 409), lower := (rows 51 70 133 328 48 32 64 128 256), losses := [] }

theorem u1361 : Upper (D 0) (R 0) [50,68,129,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1361
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1362 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 133 328 144 57 121 185 313), lower := (rows 51 70 133 328 144 32 64 128 256), losses := [] }

theorem u1362 : Upper (D 0) (R 0) [50,68,129,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1362
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1363 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 51 70 133 392 17 120 120 248 376), lower := (rows 51 70 133 392 17 32 64 128 256), losses := [] }

theorem u1363 : Upper (D 0) (R 0) [50,68,129,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1363
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1364 : PairBound 9 := { available := 113, camps := [], pairs := [], upper := (rows 51 70 133 392 24 113 113 241 369), lower := (rows 51 70 133 392 24 32 64 128 256), losses := [] }

theorem u1364 : Upper (D 0) (R 0) [50,68,129,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1364
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1365 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 133 392 48 121 89 217 345), lower := (rows 51 70 133 392 48 32 64 128 256), losses := [] }

theorem u1365 : Upper (D 0) (R 0) [50,68,129,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1365
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1366 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 133 392 80 57 121 185 313), lower := (rows 51 70 133 392 80 32 64 128 256), losses := [] }

theorem u1366 : Upper (D 0) (R 0) [50,68,129,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1366
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1367 : PairBound 9 := { available := 240, camps := [], pairs := [(1,0)], upper := (rows 51 70 140 265 17 240 240 240 496), lower := (rows 51 70 140 265 17 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 49 81 145 273), good := (rows 498 70 142 494 496 32 64 128 256) }] }

theorem u1367 : Upper (D 0) (R 0) [50,68,136,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1367
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1368 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 140 265 48 241 209 209 465), lower := (rows 51 70 140 265 48 32 64 128 256), losses := [] }

theorem u1368 : Upper (D 0) (R 0) [50,68,136,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1368
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1369 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 140 265 80 177 241 177 433), lower := (rows 51 70 140 265 80 32 64 128 256), losses := [] }

theorem u1369 : Upper (D 0) (R 0) [50,68,136,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1369
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1370 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 140 265 144 113 113 241 369), lower := (rows 51 70 140 265 144 32 64 128 256), losses := [] }

theorem u1370 : Upper (D 0) (R 0) [50,68,136,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1370
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1371 : PairBound 9 := { available := 225, camps := [], pairs := [(1,4)], upper := (rows 51 70 140 280 17 225 225 225 481), lower := (rows 51 70 140 280 17 32 64 128 256), losses := [{ target := 4, region := (rows 1 10 12 8 0 49 81 145 273), good := (rows 483 70 142 494 481 32 64 128 256) }] }

theorem u1371 : Upper (D 0) (R 0) [50,68,136,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1371
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1372 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 140 280 48 225 193 193 449), lower := (rows 51 70 140 280 48 32 64 128 256), losses := [] }

theorem u1372 : Upper (D 0) (R 0) [50,68,136,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1372
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1373 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 140 280 80 161 225 161 417), lower := (rows 51 70 140 280 80 32 64 128 256), losses := [] }

theorem u1373 : Upper (D 0) (R 0) [50,68,136,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1373
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1374 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 140 280 144 97 97 225 353), lower := (rows 51 70 140 280 144 32 64 128 256), losses := [] }

theorem u1374 : Upper (D 0) (R 0) [50,68,136,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1374
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1375 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 51 70 261 88 17 168 232 168 424), lower := (rows 51 70 261 88 17 32 64 128 256), losses := [] }

theorem u1375 : Upper (D 0) (R 0) [50,68,257,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1375
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1376 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 70 261 88 24 161 225 161 417), lower := (rows 51 70 261 88 24 32 64 128 256), losses := [] }

theorem u1376 : Upper (D 0) (R 0) [50,68,257,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1376
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1377 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 261 88 48 169 201 137 393), lower := (rows 51 70 261 88 48 32 64 128 256), losses := [] }

theorem u1377 : Upper (D 0) (R 0) [50,68,257,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1377
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1378 : Route 9 := (fun mask => (mask,id))

def c1378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1378 : Upper (D 0) (R 0) [50,68,257,80,128] 13 := by
  apply FastRouting.sound _ _ [50,68,257,80,128] 13 (by decide) (choices 1) [1,8,128] r1378 c1378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u368
  · exact u369
  · exact u370

def b1379 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 70 261 137 24 240 240 240 496), lower := (rows 51 70 261 137 24 32 64 128 256), losses := [] }

theorem u1379 : Upper (D 0) (R 0) [50,68,257,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1379
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u1379
end Delivery.IrregularNine14.P00
