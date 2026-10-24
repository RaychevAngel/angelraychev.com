import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0033

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5400 : PairBound 9 := { available := 390, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 41 56 422 454 390 390), lower := (rows 7 26 69 41 56 32 64 128 256), losses := [] }

theorem u5400 : Upper (D 5) (R 5) [6,24,65,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5400
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5401 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 69 41 146 300 364 428 300), lower := (rows 7 26 69 41 146 32 64 128 256), losses := [] }

theorem u5401 : Upper (D 5) (R 5) [6,24,65,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5401
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5402 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(1,0),(3,2)], upper := (rows 7 26 69 41 148 298 362 426 298), lower := (rows 7 26 69 41 148 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 17 42 74 138 266), good := (rows 502 506 84 506 148 32 64 128 256) }] }

theorem u5402 : Upper (D 5) (R 5) [6,24,65,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5402
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5403 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 41 152 294 358 422 294), lower := (rows 7 26 69 41 152 32 64 128 256), losses := [] }

theorem u5403 : Upper (D 5) (R 5) [6,24,65,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5403
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5404 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 69 41 176 302 334 398 270), lower := (rows 7 26 69 41 176 32 64 128 256), losses := [] }

theorem u5404 : Upper (D 5) (R 5) [6,24,65,33,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5404
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5405 : Route 9 := (fun mask => (mask,id))

def c5405 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5405 : Upper (D 5) (R 5) [6,24,65,33,384] 13 := by
  apply FastRouting.sound _ _ [6,24,65,33,384] 13 (by decide) (choices 1) [2,4,8] r5405 c5405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2020
  · exact u2021
  · exact u2022

def b5406 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 426, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 42 21 424 488 424 424), lower := (rows 7 26 69 42 21 32 64 128 256), losses := [] }

theorem u5406 : Upper (D 5) (R 5) [6,24,65,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5406
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5407 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 42 25 420 484 420 420), lower := (rows 7 26 69 42 25 32 64 128 256), losses := [] }

theorem u5407 : Upper (D 5) (R 5) [6,24,65,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5407
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5408 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 484, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 26 69 42 28 417 481 417 417), lower := (rows 7 26 69 42 28 32 64 128 256), losses := [] }

theorem u5408 : Upper (D 5) (R 5) [6,24,65,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5408
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5409 : PairBound 9 := { available := 396, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 42 49 428 460 396 396), lower := (rows 7 26 69 42 49 32 64 128 256), losses := [] }

theorem u5409 : Upper (D 5) (R 5) [6,24,65,34,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5409
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5410 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 42 52 425 457 393 393), lower := (rows 7 26 69 42 52 32 64 128 256), losses := [] }

theorem u5410 : Upper (D 5) (R 5) [6,24,65,34,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5410
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5411 : PairBound 9 := { available := 389, camps := [{ cop := 5, region := 26, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 42 56 421 453 389 389), lower := (rows 7 26 69 42 56 32 64 128 256), losses := [] }

theorem u5411 : Upper (D 5) (R 5) [6,24,65,34,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5411
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5412 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 296, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 69 42 145 300 364 428 300), lower := (rows 7 26 69 42 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 25 16 37 69 133 261), good := (rows 494 26 492 42 506 32 64 128 256) }] }

theorem u5412 : Upper (D 5) (R 5) [6,24,65,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5412
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5413 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 69 42 148 297 361 425 297), lower := (rows 7 26 69 42 148 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 25 16 37 69 133 261), good := (rows 491 26 489 42 506 32 64 128 256) }] }

theorem u5413 : Upper (D 5) (R 5) [6,24,65,34,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5413
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5414 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 42 152 293 357 421 293), lower := (rows 7 26 69 42 152 32 64 128 256), losses := [] }

theorem u5414 : Upper (D 5) (R 5) [6,24,65,34,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5414
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5415 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 42 176 301 333 397 269), lower := (rows 7 26 69 42 176 32 64 128 256), losses := [] }

theorem u5415 : Upper (D 5) (R 5) [6,24,65,34,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5415
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5416 : Route 9 := (fun mask => (mask,id))

def c5416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5416 : Upper (D 5) (R 5) [6,24,65,34,384] 13 := by
  apply FastRouting.sound _ _ [6,24,65,34,384] 13 (by decide) (choices 1) [1,4,8] r5416 c5416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2023
  · exact u2024
  · exact u2025

def b5417 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 69 44 19 424 488 424 424), lower := (rows 7 26 69 44 19 32 64 128 256), losses := [] }

theorem u5417 : Upper (D 5) (R 5) [6,24,65,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5417
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5418 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 69 44 25 418 482 418 418), lower := (rows 7 26 69 44 25 32 64 128 256), losses := [] }

theorem u5418 : Upper (D 5) (R 5) [6,24,65,36,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5418
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5419 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 44 26 417 481 417 417), lower := (rows 7 26 69 44 26 32 64 128 256), losses := [] }

theorem u5419 : Upper (D 5) (R 5) [6,24,65,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5419
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5420 : PairBound 9 := { available := 394, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 69 44 49 426 458 394 394), lower := (rows 7 26 69 44 49 32 64 128 256), losses := [] }

theorem u5420 : Upper (D 5) (R 5) [6,24,65,36,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5420
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5421 : PairBound 9 := { available := 393, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 44 50 425 457 393 393), lower := (rows 7 26 69 44 50 32 64 128 256), losses := [] }

theorem u5421 : Upper (D 5) (R 5) [6,24,65,36,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5421
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5422 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 44 56 419 451 387 387), lower := (rows 7 26 69 44 56 32 64 128 256), losses := [] }

theorem u5422 : Upper (D 5) (R 5) [6,24,65,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5422
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5423 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 296, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 69 44 145 298 362 426 298), lower := (rows 7 26 69 44 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 13 16 51 83 147 275), good := (rows 494 506 492 44 506 32 64 128 256) }] }

theorem u5423 : Upper (D 5) (R 5) [6,24,65,36,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5423
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5424 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 69 44 146 297 361 425 297), lower := (rows 7 26 69 44 146 32 64 128 256), losses := [] }

theorem u5424 : Upper (D 5) (R 5) [6,24,65,36,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5424
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5425 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 44 152 291 355 419 291), lower := (rows 7 26 69 44 152 32 64 128 256), losses := [] }

theorem u5425 : Upper (D 5) (R 5) [6,24,65,36,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5425
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5426 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 69 44 176 299 331 395 267), lower := (rows 7 26 69 44 176 32 64 128 256), losses := [] }

theorem u5426 : Upper (D 5) (R 5) [6,24,65,36,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5426
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5427 : Route 9 := (fun mask => (mask,id))

def c5427 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5427 : Upper (D 5) (R 5) [6,24,65,36,384] 13 := by
  apply FastRouting.sound _ _ [6,24,65,36,384] 13 (by decide) (choices 1) [1,2,8] r5427 c5427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2026
  · exact u2027
  · exact u2028

def b5428 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 69 137 22 296 360 424 296), lower := (rows 7 26 69 137 22 32 64 128 256), losses := [] }

theorem u5428 : Upper (D 5) (R 5) [6,24,65,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5428
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5429 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 137 26 292 356 420 292), lower := (rows 7 26 69 137 26 32 64 128 256), losses := [] }

theorem u5429 : Upper (D 5) (R 5) [6,24,65,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5429
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5430 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 357, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 69 137 28 290 354 418 290), lower := (rows 7 26 69 137 28 32 64 128 256), losses := [] }

theorem u5430 : Upper (D 5) (R 5) [6,24,65,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5430
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5431 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 69 137 50 300 364 428 300), lower := (rows 7 26 69 137 50 32 64 128 256), losses := [] }

theorem u5431 : Upper (D 5) (R 5) [6,24,65,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5431
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5432 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 424, targets := 4 }], pairs := [(1,0),(3,2)], upper := (rows 7 26 69 137 52 298 362 426 298), lower := (rows 7 26 69 137 52 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 17 42 74 138 266), good := (rows 502 506 84 506 52 32 64 128 256) }] }

theorem u5432 : Upper (D 5) (R 5) [6,24,65,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5432
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5433 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 137 56 294 358 422 294), lower := (rows 7 26 69 137 56 32 64 128 256), losses := [] }

theorem u5433 : Upper (D 5) (R 5) [6,24,65,129,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5433
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5434 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 69 137 274 44 108 172 300), lower := (rows 7 26 69 137 274 32 64 128 256), losses := [] }

theorem u5434 : Upper (D 5) (R 5) [6,24,65,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5434
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5435 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 168, targets := 4 }], pairs := [(1,0),(3,2)], upper := (rows 7 26 69 137 276 42 106 170 298), lower := (rows 7 26 69 137 276 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 17 42 74 138 266), good := (rows 502 506 84 506 276 32 64 128 256) }] }

theorem u5435 : Upper (D 5) (R 5) [6,24,65,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5435
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5436 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 137 280 38 102 166 294), lower := (rows 7 26 69 137 280 32 64 128 256), losses := [] }

theorem u5436 : Upper (D 5) (R 5) [6,24,65,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5436
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5437 : Route 9 := (fun mask => (mask,id))

def c5437 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5437 : Upper (D 5) (R 5) [6,24,65,129,288] 13 := by
  apply FastRouting.sound _ _ [6,24,65,129,288] 13 (by decide) (choices 1) [2,4,8] r5437 c5437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2029
  · exact u2030
  · exact u2031

def b5438 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 426, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 138 21 296 360 424 296), lower := (rows 7 26 69 138 21 32 64 128 256), losses := [] }

theorem u5438 : Upper (D 5) (R 5) [6,24,65,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5438
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5439 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 138 25 292 356 420 292), lower := (rows 7 26 69 138 25 32 64 128 256), losses := [] }

theorem u5439 : Upper (D 5) (R 5) [6,24,65,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5439
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5440 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 356, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 26 69 138 28 289 353 417 289), lower := (rows 7 26 69 138 28 32 64 128 256), losses := [] }

theorem u5440 : Upper (D 5) (R 5) [6,24,65,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5440
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5441 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 424, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 69 138 49 300 364 428 300), lower := (rows 7 26 69 138 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 25 16 37 69 133 261), good := (rows 494 26 492 138 506 32 64 128 256) }] }

theorem u5441 : Upper (D 5) (R 5) [6,24,65,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5441
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5442 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 424, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 69 138 52 297 361 425 297), lower := (rows 7 26 69 138 52 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 25 16 37 69 133 261), good := (rows 491 26 489 138 506 32 64 128 256) }] }

theorem u5442 : Upper (D 5) (R 5) [6,24,65,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5442
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5443 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 138 56 293 357 421 293), lower := (rows 7 26 69 138 56 32 64 128 256), losses := [] }

theorem u5443 : Upper (D 5) (R 5) [6,24,65,130,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5443
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5444 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 168, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 69 138 273 44 108 172 300), lower := (rows 7 26 69 138 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 25 16 37 69 133 261), good := (rows 494 26 492 138 506 32 64 128 256) }] }

theorem u5444 : Upper (D 5) (R 5) [6,24,65,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5444
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5445 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 168, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 69 138 276 41 105 169 297), lower := (rows 7 26 69 138 276 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 25 16 37 69 133 261), good := (rows 491 26 489 138 506 32 64 128 256) }] }

theorem u5445 : Upper (D 5) (R 5) [6,24,65,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5445
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5446 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 138 280 37 101 165 293), lower := (rows 7 26 69 138 280 32 64 128 256), losses := [] }

theorem u5446 : Upper (D 5) (R 5) [6,24,65,130,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5446
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5447 : Route 9 := (fun mask => (mask,id))

def c5447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5447 : Upper (D 5) (R 5) [6,24,65,130,288] 13 := by
  apply FastRouting.sound _ _ [6,24,65,130,288] 13 (by decide) (choices 1) [1,4,8] r5447 c5447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2032
  · exact u2033
  · exact u2034

def b5448 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 69 140 19 296 360 424 296), lower := (rows 7 26 69 140 19 32 64 128 256), losses := [] }

theorem u5448 : Upper (D 5) (R 5) [6,24,65,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5448
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5449 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 69 140 25 290 354 418 290), lower := (rows 7 26 69 140 25 32 64 128 256), losses := [] }

theorem u5449 : Upper (D 5) (R 5) [6,24,65,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5449
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5450 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 140 26 289 353 417 289), lower := (rows 7 26 69 140 26 32 64 128 256), losses := [] }

theorem u5450 : Upper (D 5) (R 5) [6,24,65,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5450
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5451 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 424, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 69 140 49 298 362 426 298), lower := (rows 7 26 69 140 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 13 16 51 83 147 275), good := (rows 494 506 492 140 506 32 64 128 256) }] }

theorem u5451 : Upper (D 5) (R 5) [6,24,65,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5451
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5452 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 69 140 50 297 361 425 297), lower := (rows 7 26 69 140 50 32 64 128 256), losses := [] }

theorem u5452 : Upper (D 5) (R 5) [6,24,65,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5452
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5453 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 140 56 291 355 419 291), lower := (rows 7 26 69 140 56 32 64 128 256), losses := [] }

theorem u5453 : Upper (D 5) (R 5) [6,24,65,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5453
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5454 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 168, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 69 140 273 42 106 170 298), lower := (rows 7 26 69 140 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 13 16 51 83 147 275), good := (rows 494 506 492 140 506 32 64 128 256) }] }

theorem u5454 : Upper (D 5) (R 5) [6,24,65,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5454
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5455 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 69 140 274 41 105 169 297), lower := (rows 7 26 69 140 274 32 64 128 256), losses := [] }

theorem u5455 : Upper (D 5) (R 5) [6,24,65,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5455
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5456 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 140 280 35 99 163 291), lower := (rows 7 26 69 140 280 32 64 128 256), losses := [] }

theorem u5456 : Upper (D 5) (R 5) [6,24,65,132,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5456
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5457 : Route 9 := (fun mask => (mask,id))

def c5457 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5457 : Upper (D 5) (R 5) [6,24,65,132,288] 13 := by
  apply FastRouting.sound _ _ [6,24,65,132,288] 13 (by decide) (choices 1) [1,2,8] r5457 c5457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2035
  · exact u2036
  · exact u2037

def b5458 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 69 168 19 300 364 428 300), lower := (rows 7 26 69 168 19 32 64 128 256), losses := [] }

theorem u5458 : Upper (D 5) (R 5) [6,24,65,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5458
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5459 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 426, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 168 21 298 362 426 298), lower := (rows 7 26 69 168 21 32 64 128 256), losses := [] }

theorem u5459 : Upper (D 5) (R 5) [6,24,65,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5459
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u5459
end Delivery.IrregularNine14.P05
