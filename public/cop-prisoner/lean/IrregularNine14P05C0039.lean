import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0007

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2340 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 56 273 34 76 140 268), lower := (rows 7 35 196 56 273 34 64 128 256), losses := [] }

theorem u2340 : Upper (D 5) (R 5) [6,33,192,48,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2340
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2341 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 196 56 273 36 74 138 266), lower := (rows 7 35 196 56 273 36 64 128 256), losses := [] }

theorem u2341 : Upper (D 5) (R 5) [6,33,192,48,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2341
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2342 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 196 56 273 40 78 142 270), lower := (rows 7 35 196 56 273 40 64 128 256), losses := [] }

theorem u2342 : Upper (D 5) (R 5) [6,33,192,48,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2342
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2343 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 56 274 33 76 140 268), lower := (rows 7 35 196 56 274 33 64 128 256), losses := [] }

theorem u2343 : Upper (D 5) (R 5) [6,33,192,48,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2343
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2344 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 196 56 274 36 73 137 265), lower := (rows 7 35 196 56 274 36 64 128 256), losses := [] }

theorem u2344 : Upper (D 5) (R 5) [6,33,192,48,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2344
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2345 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 196 56 274 40 77 141 269), lower := (rows 7 35 196 56 274 40 64 128 256), losses := [] }

theorem u2345 : Upper (D 5) (R 5) [6,33,192,48,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2345
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2346 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 56 276 33 74 138 266), lower := (rows 7 35 196 56 276 33 64 128 256), losses := [] }

theorem u2346 : Upper (D 5) (R 5) [6,33,192,48,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2346
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2347 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 56 276 34 73 137 265), lower := (rows 7 35 196 56 276 34 64 128 256), losses := [] }

theorem u2347 : Upper (D 5) (R 5) [6,33,192,48,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2347
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2348 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 196 56 276 40 75 139 267), lower := (rows 7 35 196 56 276 40 64 128 256), losses := [] }

theorem u2348 : Upper (D 5) (R 5) [6,33,192,48,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2348
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2349 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 56 280 33 78 142 270), lower := (rows 7 35 196 56 280 33 64 128 256), losses := [] }

theorem u2349 : Upper (D 5) (R 5) [6,33,192,48,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2349
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2350 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 56 280 34 77 141 269), lower := (rows 7 35 196 56 280 34 64 128 256), losses := [] }

theorem u2350 : Upper (D 5) (R 5) [6,33,192,48,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2350
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2351 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 196 56 280 36 75 139 267), lower := (rows 7 35 196 56 280 36 64 128 256), losses := [] }

theorem u2351 : Upper (D 5) (R 5) [6,33,192,48,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2351
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2352 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 196 56 280 40 71 135 263), lower := (rows 7 35 196 56 280 40 64 128 256), losses := [] }

theorem u2352 : Upper (D 5) (R 5) [6,33,192,48,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2352
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2353 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 265 28 34 120 184 312), lower := (rows 7 35 196 265 28 34 64 128 256), losses := [] }

theorem u2353 : Upper (D 5) (R 5) [6,33,192,257,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2353
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2354 : Route 9 := (fun mask => (mask,id))

def c2354 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2354 : Upper (D 5) (R 5) [6,33,192,257,12,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,257,12,8] 13 (by decide) (choices 1) [2,16,32] r2354 c2354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u453
  · exact u454
  · exact u455

def b2355 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 196 265 28 48 106 170 298), lower := (rows 7 35 196 265 28 48 64 128 256), losses := [] }

theorem u2355 : Upper (D 5) (R 5) [6,33,192,257,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2355
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2356 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 265 56 34 92 156 284), lower := (rows 7 35 196 265 56 34 64 128 256), losses := [] }

theorem u2356 : Upper (D 5) (R 5) [6,33,192,257,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2356
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2357 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 196 265 56 36 90 154 282), lower := (rows 7 35 196 265 56 36 64 128 256), losses := [] }

theorem u2357 : Upper (D 5) (R 5) [6,33,192,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2357
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2358 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 196 265 56 40 86 150 278), lower := (rows 7 35 196 265 56 40 64 128 256), losses := [] }

theorem u2358 : Upper (D 5) (R 5) [6,33,192,257,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2358
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2359 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 196 265 56 48 78 142 270), lower := (rows 7 35 196 265 56 48 64 128 256), losses := [] }

theorem u2359 : Upper (D 5) (R 5) [6,33,192,257,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2359
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2360 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 266 28 33 120 184 312), lower := (rows 7 35 196 266 28 33 64 128 256), losses := [] }

theorem u2360 : Upper (D 5) (R 5) [6,33,192,258,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2360
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2361 : PairBound 9 := { available := 49, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 35 196 266 28 40 113 177 305), lower := (rows 7 35 196 266 28 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 15 8 56 56 66 130 258), good := (rows 453 501 196 508 60 60 64 128 256) }] }

theorem u2361 : Upper (D 5) (R 5) [6,33,192,258,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2361
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2362 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 196 266 28 48 105 169 297), lower := (rows 7 35 196 266 28 48 64 128 256), losses := [] }

theorem u2362 : Upper (D 5) (R 5) [6,33,192,258,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2362
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2363 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 266 56 33 92 156 284), lower := (rows 7 35 196 266 56 33 64 128 256), losses := [] }

theorem u2363 : Upper (D 5) (R 5) [6,33,192,258,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2363
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2364 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 196 266 56 36 89 153 281), lower := (rows 7 35 196 266 56 36 64 128 256), losses := [] }

theorem u2364 : Upper (D 5) (R 5) [6,33,192,258,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2364
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2365 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 196 266 56 40 85 149 277), lower := (rows 7 35 196 266 56 40 64 128 256), losses := [] }

theorem u2365 : Upper (D 5) (R 5) [6,33,192,258,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2365
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2366 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 196 266 56 48 77 141 269), lower := (rows 7 35 196 266 56 48 64 128 256), losses := [] }

theorem u2366 : Upper (D 5) (R 5) [6,33,192,258,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2366
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2367 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 268 25 34 120 184 312), lower := (rows 7 35 196 268 25 34 64 128 256), losses := [] }

theorem u2367 : Upper (D 5) (R 5) [6,33,192,260,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2367
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2368 : Route 9 := (fun mask => (mask,id))

def c2368 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2368 : Upper (D 5) (R 5) [6,33,192,260,9,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,260,9,8] 13 (by decide) (choices 1) [2,16,32] r2368 c2368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u456
  · exact u457
  · exact u458

def b2369 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 268 25 48 106 170 298), lower := (rows 7 35 196 268 25 48 64 128 256), losses := [] }

theorem u2369 : Upper (D 5) (R 5) [6,33,192,260,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2369
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2370 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 268 26 33 120 184 312), lower := (rows 7 35 196 268 26 33 64 128 256), losses := [] }

theorem u2370 : Upper (D 5) (R 5) [6,33,192,260,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2370
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2371 : Route 9 := (fun mask => (mask,id))

def c2371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2371 : Upper (D 5) (R 5) [6,33,192,260,10,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,260,10,8] 13 (by decide) (choices 1) [1,16,32] r2371 c2371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u459
  · exact u460
  · exact u461

def b2372 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 7 35 196 268 26 48 105 169 297), lower := (rows 7 35 196 268 26 48 64 128 256), losses := [] }

theorem u2372 : Upper (D 5) (R 5) [6,33,192,260,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2372
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2373 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 268 56 33 90 154 282), lower := (rows 7 35 196 268 56 33 64 128 256), losses := [] }

theorem u2373 : Upper (D 5) (R 5) [6,33,192,260,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2373
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2374 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 268 56 34 89 153 281), lower := (rows 7 35 196 268 56 34 64 128 256), losses := [] }

theorem u2374 : Upper (D 5) (R 5) [6,33,192,260,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2374
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2375 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 196 268 56 40 83 147 275), lower := (rows 7 35 196 268 56 40 64 128 256), losses := [] }

theorem u2375 : Upper (D 5) (R 5) [6,33,192,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2375
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2376 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 196 268 56 48 75 139 267), lower := (rows 7 35 196 268 56 48 64 128 256), losses := [] }

theorem u2376 : Upper (D 5) (R 5) [6,33,192,260,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2376
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2377 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 280 25 34 108 172 300), lower := (rows 7 35 196 280 25 34 64 128 256), losses := [] }

theorem u2377 : Upper (D 5) (R 5) [6,33,192,272,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2377
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2378 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 196 280 25 36 106 170 298), lower := (rows 7 35 196 280 25 36 64 128 256), losses := [] }

theorem u2378 : Upper (D 5) (R 5) [6,33,192,272,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2378
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2379 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 196 280 25 40 102 166 294), lower := (rows 7 35 196 280 25 40 64 128 256), losses := [] }

theorem u2379 : Upper (D 5) (R 5) [6,33,192,272,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2379
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2380 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 280 26 33 108 172 300), lower := (rows 7 35 196 280 26 33 64 128 256), losses := [] }

theorem u2380 : Upper (D 5) (R 5) [6,33,192,272,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2380
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2381 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 196 280 26 36 105 169 297), lower := (rows 7 35 196 280 26 36 64 128 256), losses := [] }

theorem u2381 : Upper (D 5) (R 5) [6,33,192,272,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2381
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2382 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 196 280 26 40 101 165 293), lower := (rows 7 35 196 280 26 40 64 128 256), losses := [] }

theorem u2382 : Upper (D 5) (R 5) [6,33,192,272,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2382
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2383 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 280 28 33 106 170 298), lower := (rows 7 35 196 280 28 33 64 128 256), losses := [] }

theorem u2383 : Upper (D 5) (R 5) [6,33,192,272,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2383
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2384 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 280 28 34 105 169 297), lower := (rows 7 35 196 280 28 34 64 128 256), losses := [] }

theorem u2384 : Upper (D 5) (R 5) [6,33,192,272,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2384
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2385 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 196 280 28 40 99 163 291), lower := (rows 7 35 196 280 28 40 64 128 256), losses := [] }

theorem u2385 : Upper (D 5) (R 5) [6,33,192,272,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2385
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2386 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 280 56 33 78 142 270), lower := (rows 7 35 196 280 56 33 64 128 256), losses := [] }

theorem u2386 : Upper (D 5) (R 5) [6,33,192,272,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2386
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2387 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 280 56 34 77 141 269), lower := (rows 7 35 196 280 56 34 64 128 256), losses := [] }

theorem u2387 : Upper (D 5) (R 5) [6,33,192,272,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2387
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2388 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 196 280 56 36 75 139 267), lower := (rows 7 35 196 280 56 36 64 128 256), losses := [] }

theorem u2388 : Upper (D 5) (R 5) [6,33,192,272,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2388
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2389 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 196 280 56 40 71 135 263), lower := (rows 7 35 196 280 56 40 64 128 256), losses := [] }

theorem u2389 : Upper (D 5) (R 5) [6,33,192,272,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2389
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2390 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 296 25 34 92 156 284), lower := (rows 7 35 196 296 25 34 64 128 256), losses := [] }

theorem u2390 : Upper (D 5) (R 5) [6,33,192,288,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2390
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2391 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 196 296 25 36 90 154 282), lower := (rows 7 35 196 296 25 36 64 128 256), losses := [] }

theorem u2391 : Upper (D 5) (R 5) [6,33,192,288,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2391
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2392 : PairBound 9 := { available := 22, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 196 296 25 40 86 150 278), lower := (rows 7 35 196 296 25 40 64 128 256), losses := [] }

theorem u2392 : Upper (D 5) (R 5) [6,33,192,288,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2392
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2393 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 296 25 48 78 142 270), lower := (rows 7 35 196 296 25 48 64 128 256), losses := [] }

theorem u2393 : Upper (D 5) (R 5) [6,33,192,288,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2393
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2394 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 296 28 33 90 154 282), lower := (rows 7 35 196 296 28 33 64 128 256), losses := [] }

theorem u2394 : Upper (D 5) (R 5) [6,33,192,288,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2394
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2395 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 296 28 34 89 153 281), lower := (rows 7 35 196 296 28 34 64 128 256), losses := [] }

theorem u2395 : Upper (D 5) (R 5) [6,33,192,288,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2395
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2396 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 196 296 28 40 83 147 275), lower := (rows 7 35 196 296 28 40 64 128 256), losses := [] }

theorem u2396 : Upper (D 5) (R 5) [6,33,192,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2396
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2397 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 196 296 28 48 75 139 267), lower := (rows 7 35 196 296 28 48 64 128 256), losses := [] }

theorem u2397 : Upper (D 5) (R 5) [6,33,192,288,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2397
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2398 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 400, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 25 146 36 360 424 296), lower := (rows 7 42 69 25 146 36 64 128 256), losses := [] }

theorem u2398 : Upper (D 5) (R 5) [6,40,65,17,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2398
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2399 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 325, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 25 146 40 356 420 292), lower := (rows 7 42 69 25 146 40 64 128 256), losses := [] }

theorem u2399 : Upper (D 5) (R 5) [6,40,65,17,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2399
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2399
end Delivery.IrregularNine14.P05
