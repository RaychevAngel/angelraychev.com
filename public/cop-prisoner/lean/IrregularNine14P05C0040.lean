import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0007
import IrregularNine14P05C0008

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2400 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 356, targets := 2 }], pairs := [(2,1)], upper := (rows 7 42 69 25 146 288 108 172 300), lower := (rows 7 42 69 25 146 288 64 128 256), losses := [] }

theorem u2400 : Upper (D 5) (R 5) [6,40,65,17,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2400
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2401 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 25 400 34 108 172 300), lower := (rows 7 42 69 25 400 34 64 128 256), losses := [] }

theorem u2401 : Upper (D 5) (R 5) [6,40,65,17,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2401
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2402 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 400, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 25 400 36 106 170 298), lower := (rows 7 42 69 25 400 36 64 128 256), losses := [] }

theorem u2402 : Upper (D 5) (R 5) [6,40,65,17,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2402
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2403 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 25 400 40 102 166 294), lower := (rows 7 42 69 25 400 40 64 128 256), losses := [] }

theorem u2403 : Upper (D 5) (R 5) [6,40,65,17,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2403
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2404 : PairBound 9 := { available := 296, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 42 69 26 145 36 360 424 296), lower := (rows 7 42 69 26 145 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 82 146 274), good := (rows 486 490 100 474 506 36 64 128 256) }] }

theorem u2404 : Upper (D 5) (R 5) [6,40,65,18,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2404
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2405 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 26 145 40 356 420 292), lower := (rows 7 42 69 26 145 40 64 128 256), losses := [] }

theorem u2405 : Upper (D 5) (R 5) [6,40,65,18,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2405
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2406 : Route 9 := (fun mask => (mask,id))

def c2406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2406 : Upper (D 5) (R 5) [6,40,65,18,129,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18,129,256] 13 (by decide) (choices 1) [4,8,32] r2406 c2406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u462
  · exact u463
  · exact u464

def b2407 : PairBound 9 := { available := 296, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 42 69 26 148 33 360 424 296), lower := (rows 7 42 69 26 148 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 41 17 32 98 162 290), good := (rows 478 490 92 474 148 506 64 128 256) }] }

theorem u2407 : Upper (D 5) (R 5) [6,40,65,18,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2407
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2408 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 26 148 40 353 417 289), lower := (rows 7 42 69 26 148 40 64 128 256), losses := [] }

theorem u2408 : Upper (D 5) (R 5) [6,40,65,18,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2408
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2409 : Route 9 := (fun mask => (mask,id))

def c2409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2409 : Upper (D 5) (R 5) [6,40,65,18,132,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18,132,256] 13 (by decide) (choices 1) [1,8,32] r2409 c2409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u465
  · exact u466
  · exact u467

def r2410 : Route 9 := (fun mask => (mask,id))

def c2410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2410 : Upper (D 5) (R 5) [6,40,65,18,384,1] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18,384,1] 13 (by decide) (choices 1) [4,8,32] r2410 c2410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u468
  · exact u469
  · exact u470

def r2411 : Route 9 := (fun mask => (mask,id))

def c2411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2411 : Upper (D 5) (R 5) [6,40,65,18,384,4] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18,384,4] 13 (by decide) (choices 1) [1,8,32] r2411 c2411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u471
  · exact u472
  · exact u473

def b2412 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 26 400 40 101 165 293), lower := (rows 7 42 69 26 400 40 64 128 256), losses := [] }

theorem u2412 : Upper (D 5) (R 5) [6,40,65,18,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2412
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2413 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 400, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 28 146 33 360 424 296), lower := (rows 7 42 69 28 146 33 64 128 256), losses := [] }

theorem u2413 : Upper (D 5) (R 5) [6,40,65,20,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2413
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2414 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 325, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 28 146 40 353 417 289), lower := (rows 7 42 69 28 146 40 64 128 256), losses := [] }

theorem u2414 : Upper (D 5) (R 5) [6,40,65,20,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2414
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2415 : Route 9 := (fun mask => (mask,id))

def c2415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2415 : Upper (D 5) (R 5) [6,40,65,20,130,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,20,130,256] 13 (by decide) (choices 1) [1,8,32] r2415 c2415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u474
  · exact u475
  · exact u476

def b2416 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 400, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 28 400 33 106 170 298), lower := (rows 7 42 69 28 400 33 64 128 256), losses := [] }

theorem u2416 : Upper (D 5) (R 5) [6,40,65,20,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2416
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2417 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 28 400 34 105 169 297), lower := (rows 7 42 69 28 400 34 64 128 256), losses := [] }

theorem u2417 : Upper (D 5) (R 5) [6,40,65,20,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2417
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2418 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 28 400 40 99 163 291), lower := (rows 7 42 69 28 400 40 64 128 256), losses := [] }

theorem u2418 : Upper (D 5) (R 5) [6,40,65,20,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2418
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2419 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 137 52 34 344 408 280), lower := (rows 7 42 69 137 52 34 64 128 256), losses := [] }

theorem u2419 : Upper (D 5) (R 5) [6,40,65,129,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2419
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2420 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 137 52 40 338 402 274), lower := (rows 7 42 69 137 52 40 64 128 256), losses := [] }

theorem u2420 : Upper (D 5) (R 5) [6,40,65,129,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2420
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2421 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 69 137 52 48 330 394 266), lower := (rows 7 42 69 137 52 48 64 128 256), losses := [] }

theorem u2421 : Upper (D 5) (R 5) [6,40,65,129,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2421
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2422 : PairBound 9 := { available := 26, camps := [], pairs := [(1,0)], upper := (rows 7 42 69 137 52 288 90 154 282), lower := (rows 7 42 69 137 52 288 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 17 298 72 136 264), good := (rows 54 490 84 506 52 288 64 128 288) }] }

theorem u2422 : Upper (D 5) (R 5) [6,40,65,129,36,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2422
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2423 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 137 274 36 120 184 312), lower := (rows 7 42 69 137 274 36 64 128 256), losses := [] }

theorem u2423 : Upper (D 5) (R 5) [6,40,65,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2423
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2424 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 137 274 40 116 180 308), lower := (rows 7 42 69 137 274 40 64 128 256), losses := [] }

theorem u2424 : Upper (D 5) (R 5) [6,40,65,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2424
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2425 : Route 9 := (fun mask => (mask,id))

def c2425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2425 : Upper (D 5) (R 5) [6,40,65,129,258,16] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,258,16] 13 (by decide) (choices 1) [4,8,32] r2425 c2425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u477
  · exact u478
  · exact u479

def b2426 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 137 276 34 120 184 312), lower := (rows 7 42 69 137 276 34 64 128 256), losses := [] }

theorem u2426 : Upper (D 5) (R 5) [6,40,65,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2426
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2427 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 137 276 40 114 178 306), lower := (rows 7 42 69 137 276 40 64 128 256), losses := [] }

theorem u2427 : Upper (D 5) (R 5) [6,40,65,129,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2427
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2428 : PairBound 9 := { available := 42, camps := [], pairs := [(1,0)], upper := (rows 7 42 69 137 276 48 106 170 298), lower := (rows 7 42 69 137 276 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 17 61 74 138 266), good := (rows 502 490 116 506 308 48 64 128 256) }] }

theorem u2428 : Upper (D 5) (R 5) [6,40,65,129,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2428
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2429 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 137 280 34 116 180 308), lower := (rows 7 42 69 137 280 34 64 128 256), losses := [] }

theorem u2429 : Upper (D 5) (R 5) [6,40,65,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2429
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2430 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 137 280 36 114 178 306), lower := (rows 7 42 69 137 280 36 64 128 256), losses := [] }

theorem u2430 : Upper (D 5) (R 5) [6,40,65,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2430
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2431 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 69 137 280 48 102 166 294), lower := (rows 7 42 69 137 280 48 64 128 256), losses := [] }

theorem u2431 : Upper (D 5) (R 5) [6,40,65,129,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2431
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2432 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 137 304 34 92 156 284), lower := (rows 7 42 69 137 304 34 64 128 256), losses := [] }

theorem u2432 : Upper (D 5) (R 5) [6,40,65,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2432
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2433 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 137 304 36 90 154 282), lower := (rows 7 42 69 137 304 36 64 128 256), losses := [] }

theorem u2433 : Upper (D 5) (R 5) [6,40,65,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2433
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2434 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 137 304 40 86 150 278), lower := (rows 7 42 69 137 304 40 64 128 256), losses := [] }

theorem u2434 : Upper (D 5) (R 5) [6,40,65,129,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2434
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2435 : PairBound 9 := { available := 14, camps := [{ cop := 8, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 69 137 304 48 78 142 270), lower := (rows 7 42 69 137 304 48 64 128 256), losses := [] }

theorem u2435 : Upper (D 5) (R 5) [6,40,65,129,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2435
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2436 : PairBound 9 := { available := 304, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 42 69 138 28 33 368 432 304), lower := (rows 7 42 69 138 28 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 42 17 32 96 160 288), good := (rows 30 490 84 138 28 506 64 128 256) }] }

theorem u2436 : Upper (D 5) (R 5) [6,40,65,130,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2436
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2437 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 325, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 69 138 28 48 353 417 289), lower := (rows 7 42 69 138 28 48 64 128 256), losses := [] }

theorem u2437 : Upper (D 5) (R 5) [6,40,65,130,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2437
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2438 : Route 9 := (fun mask => (mask,id))

def c2438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2438 : Upper (D 5) (R 5) [6,40,65,130,12,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,12,256] 13 (by decide) (choices 1) [1,16,32] r2438 c2438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u480
  · exact u481
  · exact u482

def b2439 : PairBound 9 := { available := 280, camps := [{ cop := 4, region := 394, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 138 49 36 344 408 280), lower := (rows 7 42 69 138 49 36 64 128 256), losses := [] }

theorem u2439 : Upper (D 5) (R 5) [6,40,65,130,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2439
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2440 : PairBound 9 := { available := 276, camps := [{ cop := 7, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 138 49 40 340 404 276), lower := (rows 7 42 69 138 49 40 64 128 256), losses := [] }

theorem u2440 : Upper (D 5) (R 5) [6,40,65,130,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2440
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2441 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 69 138 49 48 332 396 268), lower := (rows 7 42 69 138 49 48 64 128 256), losses := [] }

theorem u2441 : Upper (D 5) (R 5) [6,40,65,130,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2441
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2442 : Route 9 := (fun mask => (mask,id))

def c2442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2442 : Upper (D 5) (R 5) [6,40,65,130,33,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,33,256] 13 (by decide) (choices 1) [4,8,16] r2442 c2442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u483
  · exact u484
  · exact u485

def b2443 : PairBound 9 := { available := 280, camps := [{ cop := 4, region := 394, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 138 52 33 344 408 280), lower := (rows 7 42 69 138 52 33 64 128 256), losses := [] }

theorem u2443 : Upper (D 5) (R 5) [6,40,65,130,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2443
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2444 : PairBound 9 := { available := 273, camps := [{ cop := 7, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 138 52 40 337 401 273), lower := (rows 7 42 69 138 52 40 64 128 256), losses := [] }

theorem u2444 : Upper (D 5) (R 5) [6,40,65,130,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2444
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2445 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 69 138 52 48 329 393 265), lower := (rows 7 42 69 138 52 48 64 128 256), losses := [] }

theorem u2445 : Upper (D 5) (R 5) [6,40,65,130,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2445
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2446 : Route 9 := (fun mask => (mask,id))

def c2446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2446 : Upper (D 5) (R 5) [6,40,65,130,36,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,36,256] 13 (by decide) (choices 1) [1,8,16] r2446 c2446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u486
  · exact u487
  · exact u488

def b2447 : PairBound 9 := { available := 56, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 42 69 138 273 36 120 184 312), lower := (rows 7 42 69 138 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 80 144 272), good := (rows 38 42 100 138 506 36 64 128 256) }] }

theorem u2447 : Upper (D 5) (R 5) [6,40,65,130,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2447
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2448 : PairBound 9 := { available := 52, camps := [{ cop := 7, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 138 273 40 116 180 308), lower := (rows 7 42 69 138 273 40 64 128 256), losses := [] }

theorem u2448 : Upper (D 5) (R 5) [6,40,65,130,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2448
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2449 : Route 9 := (fun mask => (mask,id))

def c2449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2449 : Upper (D 5) (R 5) [6,40,65,130,257,16] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,257,16] 13 (by decide) (choices 1) [4,8,32] r2449 c2449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u489
  · exact u490
  · exact u491

def b2450 : PairBound 9 := { available := 56, camps := [], pairs := [(1,2),(3,2)], upper := (rows 7 42 69 138 276 33 120 184 312), lower := (rows 7 42 69 138 276 33 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 37 80 144 272), good := (rows 35 42 97 138 506 33 64 128 256) }] }

theorem u2450 : Upper (D 5) (R 5) [6,40,65,130,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2450
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2451 : PairBound 9 := { available := 49, camps := [{ cop := 7, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 138 276 40 113 177 305), lower := (rows 7 42 69 138 276 40 64 128 256), losses := [] }

theorem u2451 : Upper (D 5) (R 5) [6,40,65,130,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2451
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2452 : Route 9 := (fun mask => (mask,id))

def c2452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2452 : Upper (D 5) (R 5) [6,40,65,130,260,16] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,260,16] 13 (by decide) (choices 1) [1,8,32] r2452 c2452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u492
  · exact u493
  · exact u494

def b2453 : PairBound 9 := { available := 52, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 42 69 138 280 33 116 180 308), lower := (rows 7 42 69 138 280 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 37 8 26 37 67 131 259), good := (rows 501 508 485 472 280 485 64 128 256) }] }

theorem u2453 : Upper (D 5) (R 5) [6,40,65,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2453
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2454 : Route 9 := (fun mask => (mask,id))

def c2454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2454 : Upper (D 5) (R 5) [6,40,65,130,264,4] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,264,4] 13 (by decide) (choices 1) [1,16,32] r2454 c2454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u495
  · exact u496
  · exact u497

def b2455 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 69 138 280 48 101 165 293), lower := (rows 7 42 69 138 280 48 64 128 256), losses := [] }

theorem u2455 : Upper (D 5) (R 5) [6,40,65,130,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2455
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2456 : Route 9 := (fun mask => (mask,id))

def c2456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2456 : Upper (D 5) (R 5) [6,40,65,130,288,1] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,288,1] 13 (by decide) (choices 1) [4,8,16] r2456 c2456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u498
  · exact u499
  · exact u500

def r2457 : Route 9 := (fun mask => (mask,id))

def c2457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2457 : Upper (D 5) (R 5) [6,40,65,130,288,4] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,288,4] 13 (by decide) (choices 1) [1,8,16] r2457 c2457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u501
  · exact u502
  · exact u503

def b2458 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 138 304 40 85 149 277), lower := (rows 7 42 69 138 304 40 64 128 256), losses := [] }

theorem u2458 : Upper (D 5) (R 5) [6,40,65,130,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2458
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2459 : PairBound 9 := { available := 13, camps := [{ cop := 8, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 69 138 304 48 77 141 269), lower := (rows 7 42 69 138 304 48 64 128 256), losses := [] }

theorem u2459 : Upper (D 5) (R 5) [6,40,65,130,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2459
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2459
end Delivery.IrregularNine14.P05
