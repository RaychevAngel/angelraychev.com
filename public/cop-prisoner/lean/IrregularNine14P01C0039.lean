import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0007
import IrregularNine14P01C0008

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2340 : Route 9 := (fun mask => (mask,id))

def c2340 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2340 : Upper (D 1) (R 1) [28,33,66,384,32] 13 := by
  apply FastRouting.sound _ _ [28,33,66,384,32] 13 (by decide) (choices 1) [2,16,64,128] r2340 c2340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u447
  · exact u448
  · exact u449
  · exact u450

def b2341 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 35 70 392 80 178 242 178 434), lower := (rows 29 35 70 392 80 32 64 128 256), losses := [] }

theorem u2341 : Upper (D 1) (R 1) [28,33,66,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2341
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2342 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 35 70 392 144 114 114 242 370), lower := (rows 29 35 70 392 144 32 64 128 256), losses := [] }

theorem u2342 : Upper (D 1) (R 1) [28,33,66,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2342
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2343 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 29 35 196 266 18 240 240 240 496), lower := (rows 29 35 196 266 18 32 64 128 256), losses := [] }

theorem u2343 : Upper (D 1) (R 1) [28,33,192,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2343
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2344 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2344 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2344 : Upper (D 1) (R 1) [28,33,192,258,32] 13 := by
  apply FastRouting.sound _ _ [28,33,192,258,32] 13 (by decide) (choices 1) [2,16,64] r2344 c2344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u451
  · exact u452
  · exact u453

def b2345 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 35 196 266 80 178 242 178 434), lower := (rows 29 35 196 266 80 32 64 128 256), losses := [] }

theorem u2345 : Upper (D 1) (R 1) [28,33,192,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2345
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2346 : PairBound 9 := { available := 480, camps := [], pairs := [], upper := (rows 29 50 70 138 17 480 480 480 480), lower := (rows 29 50 70 138 17 32 64 128 256), losses := [] }

theorem u2346 : Upper (D 1) (R 1) [28,48,66,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2346
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2347 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 29 50 70 138 48 481 449 449 449), lower := (rows 29 50 70 138 48 32 64 128 256), losses := [] }

theorem u2347 : Upper (D 1) (R 1) [28,48,66,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2347
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2348 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 70 138 80 417 481 417 417), lower := (rows 29 50 70 138 80 32 64 128 256), losses := [] }

theorem u2348 : Upper (D 1) (R 1) [28,48,66,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2348
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2349 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 29 50 70 138 272 225 225 225 481), lower := (rows 29 50 70 138 272 32 64 128 256), losses := [] }

theorem u2349 : Upper (D 1) (R 1) [28,48,66,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2349
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2350 : PairBound 9 := { available := 450, camps := [], pairs := [], upper := (rows 29 50 70 168 17 482 450 450 450), lower := (rows 29 50 70 168 17 32 64 128 256), losses := [] }

theorem u2350 : Upper (D 1) (R 1) [28,48,66,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2350
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2351 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 29 50 70 168 18 481 449 449 449), lower := (rows 29 50 70 168 18 32 64 128 256), losses := [] }

theorem u2351 : Upper (D 1) (R 1) [28,48,66,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2351
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2352 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 70 168 80 419 451 387 387), lower := (rows 29 50 70 168 80 32 64 128 256), losses := [] }

theorem u2352 : Upper (D 1) (R 1) [28,48,66,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2352
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2353 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 29 50 70 168 144 355 323 451 323), lower := (rows 29 50 70 168 144 32 64 128 256), losses := [] }

theorem u2353 : Upper (D 1) (R 1) [28,48,66,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2353
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2354 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 29 50 70 168 272 227 195 195 451), lower := (rows 29 50 70 168 272 32 64 128 256), losses := [] }

theorem u2354 : Upper (D 1) (R 1) [28,48,66,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2354
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2355 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 29 50 70 266 17 224 224 224 480), lower := (rows 29 50 70 266 17 32 64 128 256), losses := [] }

theorem u2355 : Upper (D 1) (R 1) [28,48,66,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2355
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2356 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 29 50 70 266 48 225 193 193 449), lower := (rows 29 50 70 266 48 32 64 128 256), losses := [] }

theorem u2356 : Upper (D 1) (R 1) [28,48,66,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2356
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2357 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 70 266 80 161 225 161 417), lower := (rows 29 50 70 266 80 32 64 128 256), losses := [] }

theorem u2357 : Upper (D 1) (R 1) [28,48,66,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2357
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2358 : Route 9 := (fun mask => (mask,id))

def c2358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2358 : Upper (D 1) (R 1) [28,48,66,258,128] 13 := by
  apply FastRouting.sound _ _ [28,48,66,258,128] 13 (by decide) (choices 1) [1,64,128] r2358 c2358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u454
  · exact u455
  · exact u456

def b2359 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 29 50 70 296 17 226 194 194 450), lower := (rows 29 50 70 296 17 32 64 128 256), losses := [] }

theorem u2359 : Upper (D 1) (R 1) [28,48,66,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2359
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2360 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 29 50 70 296 18 225 193 193 449), lower := (rows 29 50 70 296 18 32 64 128 256), losses := [] }

theorem u2360 : Upper (D 1) (R 1) [28,48,66,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2360
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2361 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 70 296 80 163 195 131 387), lower := (rows 29 50 70 296 80 32 64 128 256), losses := [] }

theorem u2361 : Upper (D 1) (R 1) [28,48,66,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2361
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2362 : Route 9 := (fun mask => (mask,id))

def c2362 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2362 : Upper (D 1) (R 1) [28,48,66,288,128] 13 := by
  apply FastRouting.sound _ _ [28,48,66,288,128] 13 (by decide) (choices 1) [1,2,64,128] r2362 c2362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u457
  · exact u458
  · exact u459
  · exact u460

def b2363 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 29 50 70 392 17 226 226 226 482), lower := (rows 29 50 70 392 17 32 64 128 256), losses := [] }

theorem u2363 : Upper (D 1) (R 1) [28,48,66,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2363
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2364 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 29 50 70 392 18 225 225 225 481), lower := (rows 29 50 70 392 18 32 64 128 256), losses := [] }

theorem u2364 : Upper (D 1) (R 1) [28,48,66,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2364
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2365 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 29 50 70 392 48 227 195 195 451), lower := (rows 29 50 70 392 48 32 64 128 256), losses := [] }

theorem u2365 : Upper (D 1) (R 1) [28,48,66,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2365
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2366 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 70 392 80 163 227 163 419), lower := (rows 29 50 70 392 80 32 64 128 256), losses := [] }

theorem u2366 : Upper (D 1) (R 1) [28,48,66,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2366
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2367 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 50 70 392 144 99 99 227 355), lower := (rows 29 50 70 392 144 32 64 128 256), losses := [] }

theorem u2367 : Upper (D 1) (R 1) [28,48,66,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2367
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2368 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 29 50 100 266 17 226 194 194 450), lower := (rows 29 50 100 266 17 32 64 128 256), losses := [] }

theorem u2368 : Upper (D 1) (R 1) [28,48,96,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2368
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2369 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 29 50 100 266 18 225 193 193 449), lower := (rows 29 50 100 266 18 32 64 128 256), losses := [] }

theorem u2369 : Upper (D 1) (R 1) [28,48,96,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2369
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2370 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 100 266 80 163 195 131 387), lower := (rows 29 50 100 266 80 32 64 128 256), losses := [] }

theorem u2370 : Upper (D 1) (R 1) [28,48,96,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2370
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2371 : Route 9 := (fun mask => (mask,id))

def c2371 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2371 : Upper (D 1) (R 1) [28,48,96,258,128] 13 := by
  apply FastRouting.sound _ _ [28,48,96,258,128] 13 (by decide) (choices 1) [1,2,64,128] r2371 c2371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u461
  · exact u462
  · exact u463
  · exact u464

def b2372 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 29 50 100 392 17 226 194 194 450), lower := (rows 29 50 100 392 17 32 64 128 256), losses := [] }

theorem u2372 : Upper (D 1) (R 1) [28,48,96,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2372
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2373 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 100 392 18 227 195 195 451), lower := (rows 29 50 100 392 18 32 64 128 256), losses := [] }

theorem u2373 : Upper (D 1) (R 1) [28,48,96,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2373
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2374 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 100 392 80 163 195 131 387), lower := (rows 29 50 100 392 80 32 64 128 256), losses := [] }

theorem u2374 : Upper (D 1) (R 1) [28,48,96,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2374
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2375 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 50 100 392 144 99 67 195 323), lower := (rows 29 50 100 392 144 32 64 128 256), losses := [] }

theorem u2375 : Upper (D 1) (R 1) [28,48,96,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2375
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2376 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 29 50 196 266 17 226 226 226 482), lower := (rows 29 50 196 266 17 32 64 128 256), losses := [] }

theorem u2376 : Upper (D 1) (R 1) [28,48,192,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2376
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2377 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 29 50 196 266 18 225 225 225 481), lower := (rows 29 50 196 266 18 32 64 128 256), losses := [] }

theorem u2377 : Upper (D 1) (R 1) [28,48,192,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2377
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2378 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 29 50 196 266 48 227 195 195 451), lower := (rows 29 50 196 266 48 32 64 128 256), losses := [] }

theorem u2378 : Upper (D 1) (R 1) [28,48,192,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2378
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2379 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 196 266 80 163 227 163 419), lower := (rows 29 50 196 266 80 32 64 128 256), losses := [] }

theorem u2379 : Upper (D 1) (R 1) [28,48,192,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2379
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2380 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 29 50 196 296 17 226 194 194 450), lower := (rows 29 50 196 296 17 32 64 128 256), losses := [] }

theorem u2380 : Upper (D 1) (R 1) [28,48,192,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2380
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2381 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 196 296 18 227 195 195 451), lower := (rows 29 50 196 296 18 32 64 128 256), losses := [] }

theorem u2381 : Upper (D 1) (R 1) [28,48,192,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2381
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2382 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 196 296 80 163 195 131 387), lower := (rows 29 50 196 296 80 32 64 128 256), losses := [] }

theorem u2382 : Upper (D 1) (R 1) [28,48,192,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2382
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2383 : PairBound 9 := { available := 464, camps := [], pairs := [(3,5)], upper := (rows 29 98 7 138 48 496 464 464 464), lower := (rows 29 98 7 138 48 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 16 0 81 145 273), good := (rows 477 66 463 138 464 0 64 128 256) }] }

theorem u2383 : Upper (D 1) (R 1) [28,96,3,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2383
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2384 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 21, targets := 32 }], pairs := [(0,5)], upper := (rows 29 98 7 138 144 368 368 496 368), lower := (rows 29 98 7 138 144 32 64 128 256), losses := [] }

theorem u2384 : Upper (D 1) (R 1) [28,96,3,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2384
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2385 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 29 98 7 138 272 240 240 240 496), lower := (rows 29 98 7 138 272 32 64 128 256), losses := [] }

theorem u2385 : Upper (D 1) (R 1) [28,96,3,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2385
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2386 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 29 98 7 168 18 496 464 464 464), lower := (rows 29 98 7 168 18 32 64 128 256), losses := [] }

theorem u2386 : Upper (D 1) (R 1) [28,96,3,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2386
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2387 : Route 9 := (fun mask => (mask,id))

def c2387 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u2387 : Upper (D 1) (R 1) [28,96,3,160,64] 13 := by
  apply FastRouting.sound _ _ [28,96,3,160,64] 13 (by decide) (choices 1) [2,16,128,256] r2387 c2387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u465
  · exact u466
  · exact u467
  · exact u468

def b2388 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 7 168 144 370 338 466 338), lower := (rows 29 98 7 168 144 32 64 128 256), losses := [] }

theorem u2388 : Upper (D 1) (R 1) [28,96,3,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2388
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2389 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 29 98 7 168 272 242 210 210 466), lower := (rows 29 98 7 168 272 32 64 128 256), losses := [] }

theorem u2389 : Upper (D 1) (R 1) [28,96,3,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2389
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2390 : PairBound 9 := { available := 208, camps := [], pairs := [(3,5)], upper := (rows 29 98 7 266 48 240 208 208 464), lower := (rows 29 98 7 266 48 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 16 0 81 145 273), good := (rows 477 66 463 266 464 0 64 128 256) }] }

theorem u2390 : Upper (D 1) (R 1) [28,96,3,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2390
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2391 : Route 9 := (fun mask => (mask,id))

def c2391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2391 : Upper (D 1) (R 1) [28,96,3,258,128] 13 := by
  apply FastRouting.sound _ _ [28,96,3,258,128] 13 (by decide) (choices 1) [16,64,128] r2391 c2391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u469
  · exact u470
  · exact u471

def b2392 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 29 98 7 296 18 240 208 208 464), lower := (rows 29 98 7 296 18 32 64 128 256), losses := [] }

theorem u2392 : Upper (D 1) (R 1) [28,96,3,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2392
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2393 : Route 9 := (fun mask => (mask,id))

def c2393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2393 : Upper (D 1) (R 1) [28,96,3,288,64] 13 := by
  apply FastRouting.sound _ _ [28,96,3,288,64] 13 (by decide) (choices 1) [2,16,128] r2393 c2393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u472
  · exact u473
  · exact u474

def r2394 : Route 9 := (fun mask => (mask,id))

def c2394 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2394 : Upper (D 1) (R 1) [28,96,3,288,128] 13 := by
  apply FastRouting.sound _ _ [28,96,3,288,128] 13 (by decide) (choices 1) [2,16,64,128] r2394 c2394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u475
  · exact u476
  · exact u477
  · exact u478

def b2395 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 29 98 7 392 18 240 240 240 496), lower := (rows 29 98 7 392 18 32 64 128 256), losses := [] }

theorem u2395 : Upper (D 1) (R 1) [28,96,3,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2395
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2396 : Route 9 := (fun mask => (mask,id))

def c2396 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2396 : Upper (D 1) (R 1) [28,96,3,384,32] 13 := by
  apply FastRouting.sound _ _ [28,96,3,384,32] 13 (by decide) (choices 1) [2,16,64,128] r2396 c2396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u479
  · exact u480
  · exact u481
  · exact u482

def b2397 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 7 392 144 114 114 242 370), lower := (rows 29 98 7 392 144 32 64 128 256), losses := [] }

theorem u2397 : Upper (D 1) (R 1) [28,96,3,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2397
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2398 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 29 98 133 266 18 240 240 240 496), lower := (rows 29 98 133 266 18 32 64 128 256), losses := [] }

theorem u2398 : Upper (D 1) (R 1) [28,96,129,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2398
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2399 : Route 9 := (fun mask => (mask,id))

def c2399 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2399 : Upper (D 1) (R 1) [28,96,129,258,32] 13 := by
  apply FastRouting.sound _ _ [28,96,129,258,32] 13 (by decide) (choices 1) [2,16,64,128] r2399 c2399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u483
  · exact u484
  · exact u485
  · exact u486

#print axioms u2399
end Delivery.IrregularNine14.P01
