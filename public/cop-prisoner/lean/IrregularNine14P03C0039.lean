import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0007
import IrregularNine14P03C0008

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2340 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 292 73 208 161 225 161 417), lower := (rows 7 26 292 73 208 32 64 128 256), losses := [] }

theorem u2340 : Upper (D 3) (R 3) [6,24,288,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2340
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2341 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 292 104 208 161 193 129 385), lower := (rows 7 26 292 104 208 32 64 128 256), losses := [] }

theorem u2341 : Upper (D 3) (R 3) [6,24,288,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2341
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2342 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 292 200 208 33 97 161 289), lower := (rows 7 26 292 200 208 32 64 128 256), losses := [] }

theorem u2342 : Upper (D 3) (R 3) [6,24,288,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2342
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2343 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 69 25 56 480 448 448 448), lower := (rows 7 35 69 25 56 32 64 128 256), losses := [] }

theorem u2343 : Upper (D 3) (R 3) [6,33,65,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2343
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2344 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 69 25 152 480 480 480 480), lower := (rows 7 35 69 25 152 32 64 128 256), losses := [] }

theorem u2344 : Upper (D 3) (R 3) [6,33,65,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2344
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2345 : PairBound 9 := { available := 456, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 69 25 176 488 456 456 456), lower := (rows 7 35 69 25 176 32 64 128 256), losses := [] }

theorem u2345 : Upper (D 3) (R 3) [6,33,65,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2345
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2346 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 69 25 280 224 224 224 480), lower := (rows 7 35 69 25 280 32 64 128 256), losses := [] }

theorem u2346 : Upper (D 3) (R 3) [6,33,65,17,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2346
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2347 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 69 25 304 232 200 200 456), lower := (rows 7 35 69 25 304 32 64 128 256), losses := [] }

theorem u2347 : Upper (D 3) (R 3) [6,33,65,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2347
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2348 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 69 25 400 232 232 232 488), lower := (rows 7 35 69 25 400 32 64 128 256), losses := [] }

theorem u2348 : Upper (D 3) (R 3) [6,33,65,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2348
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2349 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 69 41 88 432 464 400 400), lower := (rows 7 35 69 41 88 32 64 128 256), losses := [] }

theorem u2349 : Upper (D 3) (R 3) [6,33,65,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2349
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2350 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 69 41 152 496 464 464 464), lower := (rows 7 35 69 41 152 32 64 128 256), losses := [] }

theorem u2350 : Upper (D 3) (R 3) [6,33,65,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2350
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2351 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 69 41 208 440 472 408 408), lower := (rows 7 35 69 41 208 32 64 128 256), losses := [] }

theorem u2351 : Upper (D 3) (R 3) [6,33,65,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2351
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2352 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 69 41 280 240 208 208 464), lower := (rows 7 35 69 41 280 32 64 128 256), losses := [] }

theorem u2352 : Upper (D 3) (R 3) [6,33,65,33,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2352
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2353 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 69 41 336 184 216 152 408), lower := (rows 7 35 69 41 336 32 64 128 256), losses := [] }

theorem u2353 : Upper (D 3) (R 3) [6,33,65,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2353
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2354 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 69 41 400 248 216 216 472), lower := (rows 7 35 69 41 400 32 64 128 256), losses := [] }

theorem u2354 : Upper (D 3) (R 3) [6,33,65,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2354
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2355 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 69 56 88 417 449 385 385), lower := (rows 7 35 69 56 88 32 64 128 256), losses := [] }

theorem u2355 : Upper (D 3) (R 3) [6,33,65,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2355
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2356 : PairBound 9 := { available := 456, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 69 56 145 488 456 456 456), lower := (rows 7 35 69 56 145 32 64 128 256), losses := [] }

theorem u2356 : Upper (D 3) (R 3) [6,33,65,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2356
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2357 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 69 56 152 481 449 449 449), lower := (rows 7 35 69 56 152 32 64 128 256), losses := [] }

theorem u2357 : Upper (D 3) (R 3) [6,33,65,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2357
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2358 : Route 9 := (fun mask => (mask,id))

def c2358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u2358 : Upper (D 3) (R 3) [6,33,65,48,192] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,192] 13 (by decide) (choices 1) [1,8,128,256] r2358 c2358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u475
  · exact u476
  · exact u477
  · exact u478

def b2359 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 69 56 273 232 200 200 456), lower := (rows 7 35 69 56 273 32 64 128 256), losses := [] }

theorem u2359 : Upper (D 3) (R 3) [6,33,65,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2359
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2360 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 69 56 280 225 193 193 449), lower := (rows 7 35 69 56 280 32 64 128 256), losses := [] }

theorem u2360 : Upper (D 3) (R 3) [6,33,65,48,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2360
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2361 : Route 9 := (fun mask => (mask,id))

def c2361 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2361 : Upper (D 3) (R 3) [6,33,65,48,320] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,320] 13 (by decide) (choices 1) [1,8,128] r2361 c2361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u479
  · exact u480
  · exact u481

def r2362 : Route 9 := (fun mask => (mask,id))

def c2362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2362 : Upper (D 3) (R 3) [6,33,65,48,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,384] 13 (by decide) (choices 1) [1,8,64,128] r2362 c2362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u482
  · exact u483
  · exact u484
  · exact u485

def b2363 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 104 152 433 465 401 401), lower := (rows 7 35 69 104 152 32 64 128 256), losses := [] }

theorem u2363 : Upper (D 3) (R 3) [6,33,65,96,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2363
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2364 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 104 280 177 209 145 401), lower := (rows 7 35 69 104 280 32 64 128 256), losses := [] }

theorem u2364 : Upper (D 3) (R 3) [6,33,65,96,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2364
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2365 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 104 400 185 217 153 409), lower := (rows 7 35 69 104 400 32 64 128 256), losses := [] }

theorem u2365 : Upper (D 3) (R 3) [6,33,65,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2365
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2366 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 137 152 368 368 496 368), lower := (rows 7 35 69 137 152 32 64 128 256), losses := [] }

theorem u2366 : Upper (D 3) (R 3) [6,33,65,129,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2366
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2367 : PairBound 9 := { available := 344, camps := [{ cop := 3, region := 368, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 69 137 176 376 344 472 344), lower := (rows 7 35 69 137 176 32 64 128 256), losses := [] }

theorem u2367 : Upper (D 3) (R 3) [6,33,65,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2367
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2368 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 368, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 69 137 280 240 240 240 496), lower := (rows 7 35 69 137 280 32 64 128 256), losses := [] }

theorem u2368 : Upper (D 3) (R 3) [6,33,65,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2368
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2369 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 368, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 69 137 304 248 216 216 472), lower := (rows 7 35 69 137 304 32 64 128 256), losses := [] }

theorem u2369 : Upper (D 3) (R 3) [6,33,65,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2369
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2370 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 368, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 69 137 400 120 120 248 376), lower := (rows 7 35 69 137 400 32 64 128 256), losses := [] }

theorem u2370 : Upper (D 3) (R 3) [6,33,65,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2370
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2371 : PairBound 9 := { available := 353, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 69 152 152 353 353 481 353), lower := (rows 7 35 69 152 152 32 64 128 256), losses := [] }

theorem u2371 : Upper (D 3) (R 3) [6,33,65,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2371
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2372 : PairBound 9 := { available := 329, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 152 176 361 329 457 329), lower := (rows 7 35 69 152 176 32 64 128 256), losses := [] }

theorem u2372 : Upper (D 3) (R 3) [6,33,65,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2372
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2373 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 69 152 273 232 232 232 488), lower := (rows 7 35 69 152 273 32 64 128 256), losses := [] }

theorem u2373 : Upper (D 3) (R 3) [6,33,65,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2373
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2374 : Route 9 := (fun mask => (mask,id))

def c2374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2374 : Upper (D 3) (R 3) [6,33,65,144,264] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,264] 13 (by decide) (choices 1) [1,64,128] r2374 c2374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u486
  · exact u487
  · exact u488

def r2375 : Route 9 := (fun mask => (mask,id))

def c2375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2375 : Upper (D 3) (R 3) [6,33,65,144,288] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,288] 13 (by decide) (choices 1) [1,8,64,128] r2375 c2375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u489
  · exact u490
  · exact u491
  · exact u492

def b2376 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 152 400 105 105 233 361), lower := (rows 7 35 69 152 400 32 64 128 256), losses := [] }

theorem u2376 : Upper (D 3) (R 3) [6,33,65,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2376
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2377 : Route 9 := (fun mask => (mask,id))

def c2377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2377 : Upper (D 3) (R 3) [6,33,65,160,192] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,192] 13 (by decide) (choices 1) [1,8,16,256] r2377 c2377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u493
  · exact u494
  · exact u495
  · exact u496

def b2378 : PairBound 9 := { available := 216, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 69 168 273 248 216 216 472), lower := (rows 7 35 69 168 273 32 64 128 256), losses := [] }

theorem u2378 : Upper (D 3) (R 3) [6,33,65,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2378
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2379 : Route 9 := (fun mask => (mask,id))

def c2379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2379 : Upper (D 3) (R 3) [6,33,65,160,264] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,264] 13 (by decide) (choices 1) [1,16,64,128] r2379 c2379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u497
  · exact u498
  · exact u499
  · exact u500

def r2380 : Route 9 := (fun mask => (mask,id))

def c2380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2380 : Upper (D 3) (R 3) [6,33,65,160,320] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,320] 13 (by decide) (choices 1) [1,8,16,128] r2380 c2380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u501
  · exact u502
  · exact u503
  · exact u504

def r2381 : Route 9 := (fun mask => (mask,id))

def c2381 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2381 : Upper (D 3) (R 3) [6,33,65,160,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,384] 13 (by decide) (choices 1) [1,8,16,64] r2381 c2381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u505
  · exact u506
  · exact u507
  · exact u508

def b2382 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 25 49 480 448 448 448), lower := (rows 7 35 76 25 49 32 64 128 256), losses := [] }

theorem u2382 : Upper (D 3) (R 3) [6,33,72,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2382
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2383 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 7 35 76 25 81 416 480 416 416), lower := (rows 7 35 76 25 81 32 64 128 256), losses := [] }

theorem u2383 : Upper (D 3) (R 3) [6,33,72,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2383
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2384 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 25 112 417 449 385 385), lower := (rows 7 35 76 25 112 32 64 128 256), losses := [] }

theorem u2384 : Upper (D 3) (R 3) [6,33,72,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2384
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2385 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 76 25 145 480 480 480 480), lower := (rows 7 35 76 25 145 32 64 128 256), losses := [] }

theorem u2385 : Upper (D 3) (R 3) [6,33,72,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2385
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2386 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 7 35 76 25 176 481 449 449 449), lower := (rows 7 35 76 25 176 32 64 128 256), losses := [] }

theorem u2386 : Upper (D 3) (R 3) [6,33,72,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2386
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2387 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 25 208 417 481 417 417), lower := (rows 7 35 76 25 208 32 64 128 256), losses := [] }

theorem u2387 : Upper (D 3) (R 3) [6,33,72,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2387
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2388 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 76 25 273 224 224 224 480), lower := (rows 7 35 76 25 273 32 64 128 256), losses := [] }

theorem u2388 : Upper (D 3) (R 3) [6,33,72,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2388
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2389 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 7 35 76 25 304 225 193 193 449), lower := (rows 7 35 76 25 304 32 64 128 256), losses := [] }

theorem u2389 : Upper (D 3) (R 3) [6,33,72,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2389
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2390 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 25 336 161 225 161 417), lower := (rows 7 35 76 25 336 32 64 128 256), losses := [] }

theorem u2390 : Upper (D 3) (R 3) [6,33,72,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2390
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2391 : Route 9 := (fun mask => (mask,id))

def c2391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2391 : Upper (D 3) (R 3) [6,33,72,17,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,384] 13 (by decide) (choices 1) [1,64,128] r2391 c2391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u509
  · exact u510
  · exact u511

def b2392 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 76 137 49 496 464 464 464), lower := (rows 7 35 76 137 49 32 64 128 256), losses := [] }

theorem u2392 : Upper (D 3) (R 3) [6,33,72,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2392
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2393 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 76 137 81 432 496 432 432), lower := (rows 7 35 76 137 81 32 64 128 256), losses := [] }

theorem u2393 : Upper (D 3) (R 3) [6,33,72,129,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2393
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2394 : Route 9 := (fun mask => (mask,id))

def c2394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u2394 : Upper (D 3) (R 3) [6,33,72,129,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,96] 13 (by decide) (choices 1) [1,16,128,256] r2394 c2394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u512
  · exact u513
  · exact u514
  · exact u515

def b2395 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 35 76 137 145 368 368 496 368), lower := (rows 7 35 76 137 145 32 64 128 256), losses := [] }

theorem u2395 : Upper (D 3) (R 3) [6,33,72,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2395
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2396 : Route 9 := (fun mask => (mask,id))

def c2396 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u2396 : Upper (D 3) (R 3) [6,33,72,129,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,160] 13 (by decide) (choices 1) [1,16,64,256] r2396 c2396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u516
  · exact u517
  · exact u518
  · exact u519

def r2397 : Route 9 := (fun mask => (mask,id))

def c2397 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2397 : Upper (D 3) (R 3) [6,33,72,129,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,192] 13 (by decide) (choices 1) [1,16,256] r2397 c2397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u520
  · exact u521
  · exact u522

def r2398 : Route 9 := (fun mask => (mask,id))

def c2398 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2398 : Upper (D 3) (R 3) [6,33,72,129,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,257] 13 (by decide) (choices 1) [16,64,128] r2398 c2398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u523
  · exact u524
  · exact u525

def r2399 : Route 9 := (fun mask => (mask,id))

def c2399 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2399 : Upper (D 3) (R 3) [6,33,72,129,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,288] 13 (by decide) (choices 1) [1,16,64,128] r2399 c2399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u526
  · exact u527
  · exact u528
  · exact u529

#print axioms u2399
end Delivery.IrregularNine14.P03
