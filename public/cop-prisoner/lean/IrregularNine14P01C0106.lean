import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0041
import IrregularNine14P01C0042

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6360 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 14 28 496 480 480 480 480), lower := (rows 51 67 14 28 16 32 64 128 256), losses := [] }

theorem u6360 : Upper (D 1) (R 1) [50,65,10,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6360
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6361 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 51 67 14 76 432 432 496 432 432), lower := (rows 51 67 14 76 16 32 64 128 256), losses := [] }

theorem u6361 : Upper (D 1) (R 1) [50,65,10,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6361
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6362 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 14 88 436 420 484 420 420), lower := (rows 51 67 14 88 16 32 64 128 256), losses := [] }

theorem u6362 : Upper (D 1) (R 1) [50,65,10,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6362
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6363 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 14 140 496 496 496 496 496), lower := (rows 51 67 14 140 16 32 64 128 256), losses := [] }

theorem u6363 : Upper (D 1) (R 1) [50,65,10,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6363
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6364 : PairBound 9 := { available := 484, camps := [{ cop := 2, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 14 152 500 484 484 484 484), lower := (rows 51 67 14 152 16 32 64 128 256), losses := [] }

theorem u6364 : Upper (D 1) (R 1) [50,65,10,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6364
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6365 : PairBound 9 := { available := 436, camps := [{ cop := 2, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 14 200 436 436 500 436 436), lower := (rows 51 67 14 200 16 32 64 128 256), losses := [] }

theorem u6365 : Upper (D 1) (R 1) [50,65,10,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6365
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6366 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 14 268 240 240 240 240 496), lower := (rows 51 67 14 268 16 32 64 128 256), losses := [] }

theorem u6366 : Upper (D 1) (R 1) [50,65,10,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6366
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6367 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 14 280 244 228 228 228 484), lower := (rows 51 67 14 280 16 32 64 128 256), losses := [] }

theorem u6367 : Upper (D 1) (R 1) [50,65,10,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6367
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6368 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 14 328 180 180 244 180 436), lower := (rows 51 67 14 328 16 32 64 128 256), losses := [] }

theorem u6368 : Upper (D 1) (R 1) [50,65,10,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6368
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6369 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 14 392 244 244 244 244 500), lower := (rows 51 67 14 392 16 32 64 128 256), losses := [] }

theorem u6369 : Upper (D 1) (R 1) [50,65,10,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6369
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6370 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 22 44 472 488 456 456 456), lower := (rows 51 67 22 44 16 32 64 128 256), losses := [] }

theorem u6370 : Upper (D 1) (R 1) [50,65,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6370
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6371 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 22 76 440 424 488 424 424), lower := (rows 51 67 22 76 16 32 64 128 256), losses := [] }

theorem u6371 : Upper (D 1) (R 1) [50,65,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6371
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6372 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 22 104 412 428 460 396 396), lower := (rows 51 67 22 104 16 32 64 128 256), losses := [] }

theorem u6372 : Upper (D 1) (R 1) [50,65,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6372
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6373 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 22 140 504 488 488 488 488), lower := (rows 51 67 22 140 16 32 64 128 256), losses := [] }

theorem u6373 : Upper (D 1) (R 1) [50,65,18,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6373
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6374 : PairBound 9 := { available := 460, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 22 168 476 492 460 460 460), lower := (rows 51 67 22 168 16 32 64 128 256), losses := [] }

theorem u6374 : Upper (D 1) (R 1) [50,65,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6374
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6375 : PairBound 9 := { available := 428, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 22 200 444 428 492 428 428), lower := (rows 51 67 22 200 16 32 64 128 256), losses := [] }

theorem u6375 : Upper (D 1) (R 1) [50,65,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6375
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6376 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 22 268 248 232 232 232 488), lower := (rows 51 67 22 268 16 32 64 128 256), losses := [] }

theorem u6376 : Upper (D 1) (R 1) [50,65,18,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6376
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6377 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 22 296 220 236 204 204 460), lower := (rows 51 67 22 296 16 32 64 128 256), losses := [] }

theorem u6377 : Upper (D 1) (R 1) [50,65,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6377
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6378 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 22 328 188 172 236 172 428), lower := (rows 51 67 22 328 16 32 64 128 256), losses := [] }

theorem u6378 : Upper (D 1) (R 1) [50,65,18,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6378
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6379 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 22 392 252 236 236 236 492), lower := (rows 51 67 22 392 16 32 64 128 256), losses := [] }

theorem u6379 : Upper (D 1) (R 1) [50,65,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6379
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6380 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 28 44 466 482 450 450 450), lower := (rows 51 67 28 44 16 32 64 128 256), losses := [] }

theorem u6380 : Upper (D 1) (R 1) [50,65,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6380
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6381 : PairBound 9 := { available := 420, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 67 28 74 436 420 484 420 420), lower := (rows 51 67 28 74 16 32 64 128 256), losses := [] }

theorem u6381 : Upper (D 1) (R 1) [50,65,24,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6381
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6382 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 67 28 76 434 418 482 418 418), lower := (rows 51 67 28 76 16 32 64 128 256), losses := [] }

theorem u6382 : Upper (D 1) (R 1) [50,65,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6382
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6383 : Route 9 := (fun mask => (mask,id))

def c6383 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 64 => 6 | _ => 0)

theorem u6383 : Upper (D 1) (R 1) [50,65,24,96] 13 := by
  apply FastRouting.sound _ _ [50,65,24,96] 13 (by decide) (choices 1) [2,4,128,256] r6383 c6383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2512
  · exact u2513
  · exact u2514
  · exact u2515

def b6384 : PairBound 9 := { available := 484, camps := [{ cop := 3, region := 372, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 28 138 500 484 484 484 484), lower := (rows 51 67 28 138 16 32 64 128 256), losses := [] }

theorem u6384 : Upper (D 1) (R 1) [50,65,24,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6384
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6385 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 67 28 140 498 482 482 482 482), lower := (rows 51 67 28 140 16 32 64 128 256), losses := [] }

theorem u6385 : Upper (D 1) (R 1) [50,65,24,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6385
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6386 : Route 9 := (fun mask => (mask,id))

def c6386 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | _ => 0)

theorem u6386 : Upper (D 1) (R 1) [50,65,24,160] 13 := by
  apply FastRouting.sound _ _ [50,65,24,160] 13 (by decide) (choices 1) [2,4,64,128,256] r6386 c6386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2516
  · exact u2517
  · exact u2518
  · exact u2519
  · exact u2520

def r6387 : Route 9 := (fun mask => (mask,id))

def c6387 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | _ => 0)

theorem u6387 : Upper (D 1) (R 1) [50,65,24,192] 13 := by
  apply FastRouting.sound _ _ [50,65,24,192] 13 (by decide) (choices 1) [2,4,32,128,256] r6387 c6387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2521
  · exact u2522
  · exact u2523
  · exact u2524
  · exact u2525

def b6388 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 28 266 244 228 228 228 484), lower := (rows 51 67 28 266 16 32 64 128 256), losses := [] }

theorem u6388 : Upper (D 1) (R 1) [50,65,24,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6388
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6389 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 51 67 28 268 242 226 226 226 482), lower := (rows 51 67 28 268 16 32 64 128 256), losses := [] }

theorem u6389 : Upper (D 1) (R 1) [50,65,24,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6389
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6390 : Route 9 := (fun mask => (mask,id))

def c6390 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6390 : Upper (D 1) (R 1) [50,65,24,288] 13 := by
  apply FastRouting.sound _ _ [50,65,24,288] 13 (by decide) (choices 1) [2,4,64,128] r6390 c6390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2526
  · exact u2527
  · exact u2528
  · exact u2529

def r6391 : Route 9 := (fun mask => (mask,id))

def c6391 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6391 : Upper (D 1) (R 1) [50,65,24,320] 13 := by
  apply FastRouting.sound _ _ [50,65,24,320] 13 (by decide) (choices 1) [2,4,32,128] r6391 c6391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2530
  · exact u2531
  · exact u2532
  · exact u2533

def r6392 : Route 9 := (fun mask => (mask,id))

def c6392 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u6392 : Upper (D 1) (R 1) [50,65,24,384] 13 := by
  apply FastRouting.sound _ _ [50,65,24,384] 13 (by decide) (choices 1) [2,4,32,64,128] r6392 c6392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2534
  · exact u2535
  · exact u2536
  · exact u2537
  · exact u2538

def b6393 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 52 76 410 426 458 394 394), lower := (rows 51 67 52 76 16 32 64 128 256), losses := [] }

theorem u6393 : Upper (D 1) (R 1) [50,65,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6393
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6394 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 52 140 474 490 458 458 458), lower := (rows 51 67 52 140 16 32 64 128 256), losses := [] }

theorem u6394 : Upper (D 1) (R 1) [50,65,48,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6394
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6395 : PairBound 9 := { available := 398, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 52 200 414 430 462 398 398), lower := (rows 51 67 52 200 16 32 64 128 256), losses := [] }

theorem u6395 : Upper (D 1) (R 1) [50,65,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6395
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6396 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 52 268 218 234 202 202 458), lower := (rows 51 67 52 268 16 32 64 128 256), losses := [] }

theorem u6396 : Upper (D 1) (R 1) [50,65,48,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6396
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6397 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 52 328 158 174 206 142 398), lower := (rows 51 67 52 328 16 32 64 128 256), losses := [] }

theorem u6397 : Upper (D 1) (R 1) [50,65,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6397
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6398 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 52 392 222 238 206 206 462), lower := (rows 51 67 52 392 16 32 64 128 256), losses := [] }

theorem u6398 : Upper (D 1) (R 1) [50,65,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6398
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6399 : PairBound 9 := { available := 440, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 67 70 140 440 440 504 440 440), lower := (rows 51 67 70 140 16 32 64 128 256), losses := [] }

theorem u6399 : Upper (D 1) (R 1) [50,65,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6399
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6400 : PairBound 9 := { available := 428, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 67 70 152 444 428 492 428 428), lower := (rows 51 67 70 152 16 32 64 128 256), losses := [] }

theorem u6400 : Upper (D 1) (R 1) [50,65,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6400
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6401 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 67 70 268 184 184 248 184 440), lower := (rows 51 67 70 268 16 32 64 128 256), losses := [] }

theorem u6401 : Upper (D 1) (R 1) [50,65,66,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6401
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6402 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 67 70 280 188 172 236 172 428), lower := (rows 51 67 70 280 16 32 64 128 256), losses := [] }

theorem u6402 : Upper (D 1) (R 1) [50,65,66,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6402
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6403 : PairBound 9 := { available := 188, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 67 70 392 188 188 252 188 444), lower := (rows 51 67 70 392 16 32 64 128 256), losses := [] }

theorem u6403 : Upper (D 1) (R 1) [50,65,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6403
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6404 : PairBound 9 := { available := 436, camps := [{ cop := 3, region := 372, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 76 138 436 436 500 436 436), lower := (rows 51 67 76 138 16 32 64 128 256), losses := [] }

theorem u6404 : Upper (D 1) (R 1) [50,65,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6404
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6405 : PairBound 9 := { available := 434, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 67 76 140 434 434 498 434 434), lower := (rows 51 67 76 140 16 32 64 128 256), losses := [] }

theorem u6405 : Upper (D 1) (R 1) [50,65,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6405
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6406 : Route 9 := (fun mask => (mask,id))

def c6406 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | _ => 0)

theorem u6406 : Upper (D 1) (R 1) [50,65,72,144] 13 := by
  apply FastRouting.sound _ _ [50,65,72,144] 13 (by decide) (choices 1) [2,4,32,128,256] r6406 c6406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2539
  · exact u2540
  · exact u2541
  · exact u2542
  · exact u2543

def b6407 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 76 266 180 180 244 180 436), lower := (rows 51 67 76 266 16 32 64 128 256), losses := [] }

theorem u6407 : Upper (D 1) (R 1) [50,65,72,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6407
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6408 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 67 76 268 178 178 242 178 434), lower := (rows 51 67 76 268 16 32 64 128 256), losses := [] }

theorem u6408 : Upper (D 1) (R 1) [50,65,72,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6408
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6409 : Route 9 := (fun mask => (mask,id))

def c6409 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6409 : Upper (D 1) (R 1) [50,65,72,272] 13 := by
  apply FastRouting.sound _ _ [50,65,72,272] 13 (by decide) (choices 1) [2,4,32,128] r6409 c6409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2544
  · exact u2545
  · exact u2546
  · exact u2547

def r6410 : Route 9 := (fun mask => (mask,id))

def c6410 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6410 : Upper (D 1) (R 1) [50,65,72,384] 13 := by
  apply FastRouting.sound _ _ [50,65,72,384] 13 (by decide) (choices 1) [2,4,32,128] r6410 c6410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2548
  · exact u2549
  · exact u2550
  · exact u2551

def b6411 : PairBound 9 := { available := 428, camps := [{ cop := 3, region := 372, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 84 138 444 428 492 428 428), lower := (rows 51 67 84 138 16 32 64 128 256), losses := [] }

theorem u6411 : Upper (D 1) (R 1) [50,65,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6411
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6412 : Route 9 := (fun mask => (mask,id))

def c6412 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | _ => 0)

theorem u6412 : Upper (D 1) (R 1) [50,65,80,132] 13 := by
  apply FastRouting.sound _ _ [50,65,80,132] 13 (by decide) (choices 1) [2,8,32,128,256] r6412 c6412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2552
  · exact u2553
  · exact u2554
  · exact u2555
  · exact u2556

def r6413 : Route 9 := (fun mask => (mask,id))

def c6413 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | _ => 0)

theorem u6413 : Upper (D 1) (R 1) [50,65,80,160] 13 := by
  apply FastRouting.sound _ _ [50,65,80,160] 13 (by decide) (choices 1) [2,4,8,128,256] r6413 c6413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2557
  · exact u2558
  · exact u2559
  · exact u2560
  · exact u2561

def b6414 : PairBound 9 := { available := 172, camps := [{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 84 266 188 172 236 172 428), lower := (rows 51 67 84 266 16 32 64 128 256), losses := [] }

theorem u6414 : Upper (D 1) (R 1) [50,65,80,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6414
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6415 : Route 9 := (fun mask => (mask,id))

def c6415 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6415 : Upper (D 1) (R 1) [50,65,80,260] 13 := by
  apply FastRouting.sound _ _ [50,65,80,260] 13 (by decide) (choices 1) [2,8,32,128] r6415 c6415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2562
  · exact u2563
  · exact u2564
  · exact u2565

def r6416 : Route 9 := (fun mask => (mask,id))

def c6416 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6416 : Upper (D 1) (R 1) [50,65,80,288] 13 := by
  apply FastRouting.sound _ _ [50,65,80,288] 13 (by decide) (choices 1) [2,4,8,128] r6416 c6416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2566
  · exact u2567
  · exact u2568
  · exact u2569

def r6417 : Route 9 := (fun mask => (mask,id))

def c6417 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 256 => 8 | _ => 0)

theorem u6417 : Upper (D 1) (R 1) [50,65,80,384] 13 := by
  apply FastRouting.sound _ _ [50,65,80,384] 13 (by decide) (choices 1) [2,4,8,32,128] r6417 c6417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2570
  · exact u2571
  · exact u2572
  · exact u2573
  · exact u2574

def b6418 : PairBound 9 := { available := 376, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 67 134 140 376 376 376 504 376), lower := (rows 51 67 134 140 16 32 64 128 256), losses := [] }

theorem u6418 : Upper (D 1) (R 1) [50,65,130,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6418
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6419 : PairBound 9 := { available := 364, camps := [{ cop := 2, region := 376, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 134 152 380 364 364 492 364), lower := (rows 51 67 134 152 16 32 64 128 256), losses := [] }

theorem u6419 : Upper (D 1) (R 1) [50,65,130,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6419
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u6419
end Delivery.IrregularNine14.P01
