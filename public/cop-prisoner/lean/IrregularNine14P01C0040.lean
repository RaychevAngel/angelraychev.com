import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0008

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2400 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 133 266 144 114 114 242 370), lower := (rows 29 98 133 266 144 32 64 128 256), losses := [] }

theorem u2400 : Upper (D 1) (R 1) [28,96,129,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2400
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2401 : PairBound 9 := { available := 210, camps := [], pairs := [(2,5)], upper := (rows 29 98 133 296 18 242 210 210 466), lower := (rows 29 98 133 296 18 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 8 18 0 82 146 274), good := (rows 477 466 133 264 466 0 64 128 256) }] }

theorem u2401 : Upper (D 1) (R 1) [28,96,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2401
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2402 : Route 9 := (fun mask => (mask,id))

def c2402 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2402 : Upper (D 1) (R 1) [28,96,129,288,64] 13 := by
  apply FastRouting.sound _ _ [28,96,129,288,64] 13 (by decide) (choices 1) [2,16,128] r2402 c2402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u487
  · exact u488
  · exact u489

def b2403 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 133 296 144 114 82 210 338), lower := (rows 29 98 133 296 144 32 64 128 256), losses := [] }

theorem u2403 : Upper (D 1) (R 1) [28,96,129,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2403
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2404 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 29 98 134 265 18 240 240 240 496), lower := (rows 29 98 134 265 18 32 64 128 256), losses := [] }

theorem u2404 : Upper (D 1) (R 1) [28,96,130,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2404
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2405 : Route 9 := (fun mask => (mask,id))

def c2405 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2405 : Upper (D 1) (R 1) [28,96,130,257,32] 13 := by
  apply FastRouting.sound _ _ [28,96,130,257,32] 13 (by decide) (choices 1) [2,16,64,128] r2405 c2405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u490
  · exact u491
  · exact u492
  · exact u493

def b2406 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 134 265 144 114 114 242 370), lower := (rows 29 98 134 265 144 32 64 128 256), losses := [] }

theorem u2406 : Upper (D 1) (R 1) [28,96,130,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2406
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2407 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 29 98 134 266 17 240 240 240 496), lower := (rows 29 98 134 266 17 32 64 128 256), losses := [] }

theorem u2407 : Upper (D 1) (R 1) [28,96,130,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2407
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2408 : Route 9 := (fun mask => (mask,id))

def c2408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2408 : Upper (D 1) (R 1) [28,96,130,258,32] 13 := by
  apply FastRouting.sound _ _ [28,96,130,258,32] 13 (by decide) (choices 1) [1,16,64,128] r2408 c2408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u494
  · exact u495
  · exact u496
  · exact u497

def b2409 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 134 266 144 113 113 241 369), lower := (rows 29 98 134 266 144 32 64 128 256), losses := [] }

theorem u2409 : Upper (D 1) (R 1) [28,96,130,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2409
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2410 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 29 98 134 296 17 242 210 210 466), lower := (rows 29 98 134 296 17 32 64 128 256), losses := [] }

theorem u2410 : Upper (D 1) (R 1) [28,96,130,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2410
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2411 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 29 98 134 296 18 241 209 209 465), lower := (rows 29 98 134 296 18 32 64 128 256), losses := [] }

theorem u2411 : Upper (D 1) (R 1) [28,96,130,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2411
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2412 : Route 9 := (fun mask => (mask,id))

def c2412 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2412 : Upper (D 1) (R 1) [28,96,130,288,64] 13 := by
  apply FastRouting.sound _ _ [28,96,130,288,64] 13 (by decide) (choices 1) [1,2,16,128] r2412 c2412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u498
  · exact u499
  · exact u500
  · exact u501

def b2413 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 134 296 144 115 83 211 339), lower := (rows 29 98 134 296 144 32 64 128 256), losses := [] }

theorem u2413 : Upper (D 1) (R 1) [28,96,130,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2413
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2414 : PairBound 9 := { available := 210, camps := [], pairs := [(3,5)], upper := (rows 29 98 164 265 18 242 210 210 466), lower := (rows 29 98 164 265 18 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 18 0 82 146 274), good := (rows 477 466 132 265 466 0 64 128 256) }] }

theorem u2414 : Upper (D 1) (R 1) [28,96,160,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2414
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2415 : Route 9 := (fun mask => (mask,id))

def c2415 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2415 : Upper (D 1) (R 1) [28,96,160,257,64] 13 := by
  apply FastRouting.sound _ _ [28,96,160,257,64] 13 (by decide) (choices 1) [2,16,128] r2415 c2415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u502
  · exact u503
  · exact u504

def b2416 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 164 265 144 114 82 210 338), lower := (rows 29 98 164 265 144 32 64 128 256), losses := [] }

theorem u2416 : Upper (D 1) (R 1) [28,96,160,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2416
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2417 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 29 98 164 266 17 242 210 210 466), lower := (rows 29 98 164 266 17 32 64 128 256), losses := [] }

theorem u2417 : Upper (D 1) (R 1) [28,96,160,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2417
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2418 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 29 98 164 266 18 241 209 209 465), lower := (rows 29 98 164 266 18 32 64 128 256), losses := [] }

theorem u2418 : Upper (D 1) (R 1) [28,96,160,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2418
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2419 : Route 9 := (fun mask => (mask,id))

def c2419 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2419 : Upper (D 1) (R 1) [28,96,160,258,64] 13 := by
  apply FastRouting.sound _ _ [28,96,160,258,64] 13 (by decide) (choices 1) [1,2,16,128] r2419 c2419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u505
  · exact u506
  · exact u507
  · exact u508

def b2420 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 164 266 144 115 83 211 339), lower := (rows 29 98 164 266 144 32 64 128 256), losses := [] }

theorem u2420 : Upper (D 1) (R 1) [28,96,160,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2420
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2421 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 29 98 164 328 17 178 210 146 402), lower := (rows 29 98 164 328 17 32 64 128 256), losses := [] }

theorem u2421 : Upper (D 1) (R 1) [28,96,160,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2421
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2422 : Route 9 := (fun mask => (mask,id))

def c2422 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2422 : Upper (D 1) (R 1) [28,96,160,320,2] 13 := by
  apply FastRouting.sound _ _ [28,96,160,320,2] 13 (by decide) (choices 1) [1,2,16,128] r2422 c2422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u509
  · exact u510
  · exact u511
  · exact u512

def b2423 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 164 328 144 51 83 147 275), lower := (rows 29 98 164 328 144 32 64 128 256), losses := [] }

theorem u2423 : Upper (D 1) (R 1) [28,96,160,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2423
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2424 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 29 259 38 74 48 240 208 208 464), lower := (rows 29 259 38 74 48 32 64 128 256), losses := [] }

theorem u2424 : Upper (D 1) (R 1) [28,257,34,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2424
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2425 : Route 9 := (fun mask => (mask,id))

def c2425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2425 : Upper (D 1) (R 1) [28,257,34,66,128] 13 := by
  apply FastRouting.sound _ _ [28,257,34,66,128] 13 (by decide) (choices 1) [16,64,128] r2425 c2425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u513
  · exact u514
  · exact u515

def b2426 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 29 259 38 200 18 240 240 240 496), lower := (rows 29 259 38 200 18 32 64 128 256), losses := [] }

theorem u2426 : Upper (D 1) (R 1) [28,257,34,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2426
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2427 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 29 259 38 200 48 242 210 210 466), lower := (rows 29 259 38 200 48 32 64 128 256), losses := [] }

theorem u2427 : Upper (D 1) (R 1) [28,257,34,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2427
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2428 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 259 38 200 80 178 242 178 434), lower := (rows 29 259 38 200 80 32 64 128 256), losses := [] }

theorem u2428 : Upper (D 1) (R 1) [28,257,34,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2428
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2429 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 29 274 38 74 17 224 224 224 480), lower := (rows 29 274 38 74 17 32 64 128 256), losses := [] }

theorem u2429 : Upper (D 1) (R 1) [28,272,34,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2429
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2430 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 29 274 38 74 48 225 193 193 449), lower := (rows 29 274 38 74 48 32 64 128 256), losses := [] }

theorem u2430 : Upper (D 1) (R 1) [28,272,34,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2430
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2431 : Route 9 := (fun mask => (mask,id))

def c2431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2431 : Upper (D 1) (R 1) [28,272,34,66,128] 13 := by
  apply FastRouting.sound _ _ [28,272,34,66,128] 13 (by decide) (choices 1) [1,64,128] r2431 c2431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u516
  · exact u517
  · exact u518

def b2432 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 29 274 38 200 17 226 226 226 482), lower := (rows 29 274 38 200 17 32 64 128 256), losses := [] }

theorem u2432 : Upper (D 1) (R 1) [28,272,34,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2432
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2433 : PairBound 9 := { available := 225, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 29 274 38 200 18 225 225 225 481), lower := (rows 29 274 38 200 18 32 64 128 256), losses := [] }

theorem u2433 : Upper (D 1) (R 1) [28,272,34,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2433
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2434 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 29 274 38 200 48 227 195 195 451), lower := (rows 29 274 38 200 48 32 64 128 256), losses := [] }

theorem u2434 : Upper (D 1) (R 1) [28,272,34,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2434
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2435 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 274 38 200 80 163 227 163 419), lower := (rows 29 274 38 200 80 32 64 128 256), losses := [] }

theorem u2435 : Upper (D 1) (R 1) [28,272,34,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2435
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2436 : PairBound 9 := { available := 208, camps := [], pairs := [(3,5)], upper := (rows 29 290 7 74 48 240 208 208 464), lower := (rows 29 290 7 74 48 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 16 0 81 145 273), good := (rows 477 258 463 74 464 0 64 128 256) }] }

theorem u2436 : Upper (D 1) (R 1) [28,288,3,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2436
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2437 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 21, targets := 32 }], pairs := [(0,5)], upper := (rows 29 290 7 74 80 176 240 176 432), lower := (rows 29 290 7 74 80 32 64 128 256), losses := [] }

theorem u2437 : Upper (D 1) (R 1) [28,288,3,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2437
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2438 : Route 9 := (fun mask => (mask,id))

def c2438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2438 : Upper (D 1) (R 1) [28,288,3,66,128] 13 := by
  apply FastRouting.sound _ _ [28,288,3,66,128] 13 (by decide) (choices 1) [16,64,128] r2438 c2438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u519
  · exact u520
  · exact u521

def b2439 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 29 290 7 104 18 240 208 208 464), lower := (rows 29 290 7 104 18 32 64 128 256), losses := [] }

theorem u2439 : Upper (D 1) (R 1) [28,288,3,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2439
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2440 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 7 104 80 178 210 146 402), lower := (rows 29 290 7 104 80 32 64 128 256), losses := [] }

theorem u2440 : Upper (D 1) (R 1) [28,288,3,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2440
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2441 : Route 9 := (fun mask => (mask,id))

def c2441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2441 : Upper (D 1) (R 1) [28,288,3,96,128] 13 := by
  apply FastRouting.sound _ _ [28,288,3,96,128] 13 (by decide) (choices 1) [2,16,64,128] r2441 c2441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u522
  · exact u523
  · exact u524
  · exact u525

def b2442 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 29 290 7 200 18 240 240 240 496), lower := (rows 29 290 7 200 18 32 64 128 256), losses := [] }

theorem u2442 : Upper (D 1) (R 1) [28,288,3,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2442
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2443 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2443 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2443 : Upper (D 1) (R 1) [28,288,3,192,32] 13 := by
  apply FastRouting.sound _ _ [28,288,3,192,32] 13 (by decide) (choices 1) [2,16,64] r2443 c2443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u526
  · exact u527
  · exact u528

def b2444 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 7 200 80 178 242 178 434), lower := (rows 29 290 7 200 80 32 64 128 256), losses := [] }

theorem u2444 : Upper (D 1) (R 1) [28,288,3,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2444
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2445 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 29 290 69 138 18 240 240 240 496), lower := (rows 29 290 69 138 18 32 64 128 256), losses := [] }

theorem u2445 : Upper (D 1) (R 1) [28,288,65,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2445
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2446 : Route 9 := (fun mask => (mask,id))

def c2446 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2446 : Upper (D 1) (R 1) [28,288,65,130,32] 13 := by
  apply FastRouting.sound _ _ [28,288,65,130,32] 13 (by decide) (choices 1) [2,16,64,128] r2446 c2446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u529
  · exact u530
  · exact u531
  · exact u532

def b2447 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 69 138 80 178 242 178 434), lower := (rows 29 290 69 138 80 32 64 128 256), losses := [] }

theorem u2447 : Upper (D 1) (R 1) [28,288,65,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2447
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2448 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 29 290 69 138 144 114 114 242 370), lower := (rows 29 290 69 138 144 32 64 128 256), losses := [] }

theorem u2448 : Upper (D 1) (R 1) [28,288,65,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2448
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2449 : PairBound 9 := { available := 210, camps := [], pairs := [(2,5)], upper := (rows 29 290 69 168 18 242 210 210 466), lower := (rows 29 290 69 168 18 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 8 18 0 82 146 274), good := (rows 477 466 69 136 466 0 64 128 256) }] }

theorem u2449 : Upper (D 1) (R 1) [28,288,65,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2449
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2450 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 69 168 80 178 210 146 402), lower := (rows 29 290 69 168 80 32 64 128 256), losses := [] }

theorem u2450 : Upper (D 1) (R 1) [28,288,65,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2450
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2451 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 29 290 69 168 144 114 82 210 338), lower := (rows 29 290 69 168 144 32 64 128 256), losses := [] }

theorem u2451 : Upper (D 1) (R 1) [28,288,65,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2451
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2452 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 29 290 70 138 17 240 240 240 496), lower := (rows 29 290 70 138 17 32 64 128 256), losses := [] }

theorem u2452 : Upper (D 1) (R 1) [28,288,66,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2452
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2453_128 : Upper (D 1) (R 1) [28,288,66,130,32,128] 13 :=
  permutation_upper _ _ _ [28,288,66,130,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u535

def r2453 : Route 9 := (fun mask => (mask,id))

def c2453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2453 : Upper (D 1) (R 1) [28,288,66,130,32] 13 := by
  apply FastRouting.sound _ _ [28,288,66,130,32] 13 (by decide) (choices 1) [1,16,64,128] r2453 c2453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u533
  · exact u534
  · exact u535
  · exact m2453_128

def b2454 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 70 138 80 177 241 177 433), lower := (rows 29 290 70 138 80 32 64 128 256), losses := [] }

theorem u2454 : Upper (D 1) (R 1) [28,288,66,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2454
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2455 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 29 290 70 168 17 242 210 210 466), lower := (rows 29 290 70 168 17 32 64 128 256), losses := [] }

theorem u2455 : Upper (D 1) (R 1) [28,288,66,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2455
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2456 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 29 290 70 168 18 241 209 209 465), lower := (rows 29 290 70 168 18 32 64 128 256), losses := [] }

theorem u2456 : Upper (D 1) (R 1) [28,288,66,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2456
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2457 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 70 168 80 179 211 147 403), lower := (rows 29 290 70 168 80 32 64 128 256), losses := [] }

theorem u2457 : Upper (D 1) (R 1) [28,288,66,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2457
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2458 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 29 290 70 168 144 115 83 211 339), lower := (rows 29 290 70 168 144 32 64 128 256), losses := [] }

theorem u2458 : Upper (D 1) (R 1) [28,288,66,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2458
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2459 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 76 152 18 480 480 480 480), lower := (rows 51 7 76 152 18 32 64 128 256), losses := [] }

theorem u2459 : Upper (D 1) (R 1) [50,5,72,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2459
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2459
end Delivery.IrregularNine14.P01
