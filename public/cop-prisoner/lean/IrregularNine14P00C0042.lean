import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0020
import IrregularNine14P00C0021
import IrregularNine14P00C0022

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2520 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 67 76 140 433 433 497 433 433), lower := (rows 51 67 76 140 16 32 64 128 256), losses := [] }

theorem u2520 : Upper (D 0) (R 0) [50,65,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2520
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2521 : Route 9 := (fun mask => (mask,id))

def c2521 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u2521 : Upper (D 0) (R 0) [50,65,72,144] 13 := by
  apply FastRouting.sound _ _ [50,65,72,144] 13 (by decide) (choices 1) [1,4,32,128,256] r2521 c2521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1240
  · exact u1241
  · exact u1242
  · exact u1243
  · exact u1244

def b2522 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 76 265 180 180 244 180 436), lower := (rows 51 67 76 265 16 32 64 128 256), losses := [] }

theorem u2522 : Upper (D 0) (R 0) [50,65,72,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2522
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2523 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 67 76 268 177 177 241 177 433), lower := (rows 51 67 76 268 16 32 64 128 256), losses := [] }

theorem u2523 : Upper (D 0) (R 0) [50,65,72,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2523
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2524 : Route 9 := (fun mask => (mask,id))

def c2524 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2524 : Upper (D 0) (R 0) [50,65,72,272] 13 := by
  apply FastRouting.sound _ _ [50,65,72,272] 13 (by decide) (choices 1) [1,4,32,128] r2524 c2524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1245
  · exact u1246
  · exact u1247
  · exact u1248

def r2525 : Route 9 := (fun mask => (mask,id))

def c2525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2525 : Upper (D 0) (R 0) [50,65,72,384] 13 := by
  apply FastRouting.sound _ _ [50,65,72,384] 13 (by decide) (choices 1) [1,4,32,128] r2525 c2525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1249
  · exact u1250
  · exact u1251
  · exact u1252

def b2526 : PairBound 9 := { available := 428, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 84 137 444 428 492 428 428), lower := (rows 51 67 84 137 16 32 64 128 256), losses := [] }

theorem u2526 : Upper (D 0) (R 0) [50,65,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2526
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2527 : Route 9 := (fun mask => (mask,id))

def c2527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u2527 : Upper (D 0) (R 0) [50,65,80,132] 13 := by
  apply FastRouting.sound _ _ [50,65,80,132] 13 (by decide) (choices 1) [1,8,32,128,256] r2527 c2527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1253
  · exact u1254
  · exact u1255
  · exact u1256
  · exact u1257

def r2528 : Route 9 := (fun mask => (mask,id))

def c2528 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 64 => 6 | _ => 0)

theorem u2528 : Upper (D 0) (R 0) [50,65,80,160] 13 := by
  apply FastRouting.sound _ _ [50,65,80,160] 13 (by decide) (choices 1) [1,4,8,128,256] r2528 c2528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1258
  · exact u1259
  · exact u1260
  · exact u1261
  · exact u1262

def b2529 : PairBound 9 := { available := 172, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 84 265 188 172 236 172 428), lower := (rows 51 67 84 265 16 32 64 128 256), losses := [] }

theorem u2529 : Upper (D 0) (R 0) [50,65,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2529
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2530 : Route 9 := (fun mask => (mask,id))

def c2530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2530 : Upper (D 0) (R 0) [50,65,80,260] 13 := by
  apply FastRouting.sound _ _ [50,65,80,260] 13 (by decide) (choices 1) [1,8,32,128] r2530 c2530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1263
  · exact u1264
  · exact u1265
  · exact u1266

def r2531 : Route 9 := (fun mask => (mask,id))

def c2531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2531 : Upper (D 0) (R 0) [50,65,80,288] 13 := by
  apply FastRouting.sound _ _ [50,65,80,288] 13 (by decide) (choices 1) [1,4,8,128] r2531 c2531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1267
  · exact u1268
  · exact u1269
  · exact u1270

def r2532 : Route 9 := (fun mask => (mask,id))

def c2532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2532 : Upper (D 0) (R 0) [50,65,80,384] 13 := by
  apply FastRouting.sound _ _ [50,65,80,384] 13 (by decide) (choices 1) [1,4,8,32,128] r2532 c2532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1271
  · exact u1272
  · exact u1273
  · exact u1274
  · exact u1275

def b2533 : PairBound 9 := { available := 376, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 67 133 140 376 376 376 504 376), lower := (rows 51 67 133 140 16 32 64 128 256), losses := [] }

theorem u2533 : Upper (D 0) (R 0) [50,65,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2533
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2534 : PairBound 9 := { available := 364, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 51 67 133 152 380 364 364 492 364), lower := (rows 51 67 133 152 16 32 64 128 256), losses := [] }

theorem u2534 : Upper (D 0) (R 0) [50,65,129,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2534
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2535 : PairBound 9 := { available := 316, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 51 67 133 200 316 316 380 444 316), lower := (rows 51 67 133 200 16 32 64 128 256), losses := [] }

theorem u2535 : Upper (D 0) (R 0) [50,65,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2535
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2536 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 51 67 133 268 248 248 248 248 504), lower := (rows 51 67 133 268 16 32 64 128 256), losses := [] }

theorem u2536 : Upper (D 0) (R 0) [50,65,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2536
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2537 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 51 67 133 280 252 236 236 236 492), lower := (rows 51 67 133 280 16 32 64 128 256), losses := [] }

theorem u2537 : Upper (D 0) (R 0) [50,65,129,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2537
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2538 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 51 67 133 328 188 188 252 188 444), lower := (rows 51 67 133 328 16 32 64 128 256), losses := [] }

theorem u2538 : Upper (D 0) (R 0) [50,65,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2538
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2539 : PairBound 9 := { available := 124, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 51 67 133 392 124 124 124 252 380), lower := (rows 51 67 133 392 16 32 64 128 256), losses := [] }

theorem u2539 : Upper (D 0) (R 0) [50,65,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2539
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2540 : PairBound 9 := { available := 369, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 140 140 369 369 369 497 369), lower := (rows 51 67 140 140 16 32 64 128 256), losses := [] }

theorem u2540 : Upper (D 0) (R 0) [50,65,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2540
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2541 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 140 152 373 357 357 485 357), lower := (rows 51 67 140 152 16 32 64 128 256), losses := [] }

theorem u2541 : Upper (D 0) (R 0) [50,65,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2541
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2542 : PairBound 9 := { available := 309, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 140 200 309 309 373 437 309), lower := (rows 51 67 140 200 16 32 64 128 256), losses := [] }

theorem u2542 : Upper (D 0) (R 0) [50,65,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2542
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2543 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 140 265 244 244 244 244 500), lower := (rows 51 67 140 265 16 32 64 128 256), losses := [] }

theorem u2543 : Upper (D 0) (R 0) [50,65,136,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2543
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2544 : Route 9 := (fun mask => (mask,id))

def c2544 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2544 : Upper (D 0) (R 0) [50,65,136,260] 13 := by
  apply FastRouting.sound _ _ [50,65,136,260] 13 (by decide) (choices 1) [1,32,64,128] r2544 c2544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1276
  · exact u1277
  · exact u1278
  · exact u1279

def r2545 : Route 9 := (fun mask => (mask,id))

def c2545 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2545 : Upper (D 0) (R 0) [50,65,136,272] 13 := by
  apply FastRouting.sound _ _ [50,65,136,272] 13 (by decide) (choices 1) [1,4,32,64,128] r2545 c2545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1280
  · exact u1281
  · exact u1282
  · exact u1283
  · exact u1284

def r2546 : Route 9 := (fun mask => (mask,id))

def c2546 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2546 : Upper (D 0) (R 0) [50,65,136,320] 13 := by
  apply FastRouting.sound _ _ [50,65,136,320] 13 (by decide) (choices 1) [1,4,32,128] r2546 c2546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1285
  · exact u1286
  · exact u1287
  · exact u1288

def b2547 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 140 392 117 117 117 245 373), lower := (rows 51 67 140 392 16 32 64 128 256), losses := [] }

theorem u2547 : Upper (D 0) (R 0) [50,65,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2547
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2548 : Route 9 := (fun mask => (mask,id))

def c2548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | _ => 0)

theorem u2548 : Upper (D 0) (R 0) [50,65,144,160] 13 := by
  apply FastRouting.sound _ _ [50,65,144,160] 13 (by decide) (choices 1) [1,4,8,64,256] r2548 c2548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1289
  · exact u1290
  · exact u1291
  · exact u1292
  · exact u1293

def r2549 : Route 9 := (fun mask => (mask,id))

def c2549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2549 : Upper (D 0) (R 0) [50,65,144,192] 13 := by
  apply FastRouting.sound _ _ [50,65,144,192] 13 (by decide) (choices 1) [1,4,8,32,256] r2549 c2549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1294
  · exact u1295
  · exact u1296
  · exact u1297
  · exact u1298

def b2550 : PairBound 9 := { available := 236, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 148 265 252 236 236 236 492), lower := (rows 51 67 148 265 16 32 64 128 256), losses := [] }

theorem u2550 : Upper (D 0) (R 0) [50,65,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2550
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2551 : Route 9 := (fun mask => (mask,id))

def c2551 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2551 : Upper (D 0) (R 0) [50,65,144,260] 13 := by
  apply FastRouting.sound _ _ [50,65,144,260] 13 (by decide) (choices 1) [1,8,32,64,128] r2551 c2551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1299
  · exact u1300
  · exact u1301
  · exact u1302
  · exact u1303

def r2552 : Route 9 := (fun mask => (mask,id))

def c2552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2552 : Upper (D 0) (R 0) [50,65,144,288] 13 := by
  apply FastRouting.sound _ _ [50,65,144,288] 13 (by decide) (choices 1) [1,4,8,64,128] r2552 c2552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1304
  · exact u1305
  · exact u1306
  · exact u1307
  · exact u1308

def r2553 : Route 9 := (fun mask => (mask,id))

def c2553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2553 : Upper (D 0) (R 0) [50,65,144,320] 13 := by
  apply FastRouting.sound _ _ [50,65,144,320] 13 (by decide) (choices 1) [1,4,8,32,128] r2553 c2553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1309
  · exact u1310
  · exact u1311
  · exact u1312
  · exact u1313

def r2554 : Route 9 := (fun mask => (mask,id))

def c2554 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2554 : Upper (D 0) (R 0) [50,65,144,384] 13 := by
  apply FastRouting.sound _ _ [50,65,144,384] 13 (by decide) (choices 1) [1,4,8,32,64] r2554 c2554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1314
  · exact u1315
  · exact u1316
  · exact u1317
  · exact u1318

def b2555 : PairBound 9 := { available := 188, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 196 265 188 188 252 188 444), lower := (rows 51 67 196 265 16 32 64 128 256), losses := [] }

theorem u2555 : Upper (D 0) (R 0) [50,65,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2555
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2556 : Route 9 := (fun mask => (mask,id))

def c2556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2556 : Upper (D 0) (R 0) [50,65,192,260] 13 := by
  apply FastRouting.sound _ _ [50,65,192,260] 13 (by decide) (choices 1) [1,8,32,128] r2556 c2556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1319
  · exact u1320
  · exact u1321
  · exact u1322

def r2557 : Route 9 := (fun mask => (mask,id))

def c2557 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2557 : Upper (D 0) (R 0) [50,65,192,272] 13 := by
  apply FastRouting.sound _ _ [50,65,192,272] 13 (by decide) (choices 1) [1,4,8,32,128] r2557 c2557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1323
  · exact u1324
  · exact u1325
  · exact u1326
  · exact u1327

def r2558 : Route 9 := (fun mask => (mask,id))

def c2558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2558 : Upper (D 0) (R 0) [50,65,192,384] 13 := by
  apply FastRouting.sound _ _ [50,65,192,384] 13 (by decide) (choices 1) [1,4,8,32] r2558 c2558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1328
  · exact u1329
  · exact u1330
  · exact u1331

def b2559 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 70 13 25 496 480 480 480 480), lower := (rows 51 70 13 25 16 32 64 128 256), losses := [] }

theorem u2559 : Upper (D 0) (R 0) [50,68,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2559
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2560 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 13 56 465 481 449 449 449), lower := (rows 51 70 13 56 16 32 64 128 256), losses := [] }

theorem u2560 : Upper (D 0) (R 0) [50,68,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2560
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2561 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 13 73 432 432 496 432 432), lower := (rows 51 70 13 73 16 32 64 128 256), losses := [] }

theorem u2561 : Upper (D 0) (R 0) [50,68,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2561
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2562 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 13 88 433 417 481 417 417), lower := (rows 51 70 13 88 16 32 64 128 256), losses := [] }

theorem u2562 : Upper (D 0) (R 0) [50,68,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2562
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2563 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 70 13 137 496 496 496 496 496), lower := (rows 51 70 13 137 16 32 64 128 256), losses := [] }

theorem u2563 : Upper (D 0) (R 0) [50,68,9,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2563
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2564 : PairBound 9 := { available := 481, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 13 152 497 481 481 481 481), lower := (rows 51 70 13 152 16 32 64 128 256), losses := [] }

theorem u2564 : Upper (D 0) (R 0) [50,68,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2564
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2565 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 13 200 433 433 497 433 433), lower := (rows 51 70 13 200 16 32 64 128 256), losses := [] }

theorem u2565 : Upper (D 0) (R 0) [50,68,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2565
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2566 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 70 13 265 240 240 240 240 496), lower := (rows 51 70 13 265 16 32 64 128 256), losses := [] }

theorem u2566 : Upper (D 0) (R 0) [50,68,9,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2566
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2567 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 13 280 241 225 225 225 481), lower := (rows 51 70 13 280 16 32 64 128 256), losses := [] }

theorem u2567 : Upper (D 0) (R 0) [50,68,9,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2567
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2568 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 13 328 177 177 241 177 433), lower := (rows 51 70 13 328 16 32 64 128 256), losses := [] }

theorem u2568 : Upper (D 0) (R 0) [50,68,9,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2568
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2569 : Route 9 := (fun mask => (mask,id))

def c2569 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2569 : Upper (D 0) (R 0) [50,68,9,384] 13 := by
  apply FastRouting.sound _ _ [50,68,9,384] 13 (by decide) (choices 1) [1,32,64,128] r2569 c2569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1332
  · exact u1333
  · exact u1334
  · exact u1335

def b2570 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 133 25 504 488 488 488 488), lower := (rows 51 70 133 25 16 32 64 128 256), losses := [] }

theorem u2570 : Upper (D 0) (R 0) [50,68,129,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2570
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2571 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 51 70 133 56 473 489 457 457 457), lower := (rows 51 70 133 56 16 32 64 128 256), losses := [] }

theorem u2571 : Upper (D 0) (R 0) [50,68,129,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2571
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2572 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 133 73 440 440 504 440 440), lower := (rows 51 70 133 73 16 32 64 128 256), losses := [] }

theorem u2572 : Upper (D 0) (R 0) [50,68,129,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2572
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2573 : Route 9 := (fun mask => (mask,id))

def c2573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u2573 : Upper (D 0) (R 0) [50,68,129,80] 13 := by
  apply FastRouting.sound _ _ [50,68,129,80] 13 (by decide) (choices 1) [1,8,32,128,256] r2573 c2573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1336
  · exact u1337
  · exact u1338
  · exact u1339
  · exact u1340

def b2574 : PairBound 9 := { available := 376, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 133 137 376 376 376 504 376), lower := (rows 51 70 133 137 16 32 64 128 256), losses := [] }

theorem u2574 : Upper (D 0) (R 0) [50,68,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2574
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2575 : Route 9 := (fun mask => (mask,id))

def c2575 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u2575 : Upper (D 0) (R 0) [50,68,129,144] 13 := by
  apply FastRouting.sound _ _ [50,68,129,144] 13 (by decide) (choices 1) [1,8,32,64,256] r2575 c2575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1341
  · exact u1342
  · exact u1343
  · exact u1344
  · exact u1345

def r2576 : Route 9 := (fun mask => (mask,id))

def c2576 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2576 : Upper (D 0) (R 0) [50,68,129,192] 13 := by
  apply FastRouting.sound _ _ [50,68,129,192] 13 (by decide) (choices 1) [1,8,32,256] r2576 c2576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1346
  · exact u1347
  · exact u1348
  · exact u1349

def r2577 : Route 9 := (fun mask => (mask,id))

def c2577 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2577 : Upper (D 0) (R 0) [50,68,129,257] 13 := by
  apply FastRouting.sound _ _ [50,68,129,257] 13 (by decide) (choices 1) [8,32,64,128] r2577 c2577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1350
  · exact u1351
  · exact u1352
  · exact u1353

def r2578 : Route 9 := (fun mask => (mask,id))

def c2578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2578 : Upper (D 0) (R 0) [50,68,129,272] 13 := by
  apply FastRouting.sound _ _ [50,68,129,272] 13 (by decide) (choices 1) [1,8,32,64,128] r2578 c2578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1354
  · exact u1355
  · exact u1356
  · exact u1357
  · exact u1358

def r2579 : Route 9 := (fun mask => (mask,id))

def c2579 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2579 : Upper (D 0) (R 0) [50,68,129,320] 13 := by
  apply FastRouting.sound _ _ [50,68,129,320] 13 (by decide) (choices 1) [1,8,32,128] r2579 c2579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1359
  · exact u1360
  · exact u1361
  · exact u1362

#print axioms u2579
end Delivery.IrregularNine14.P00
