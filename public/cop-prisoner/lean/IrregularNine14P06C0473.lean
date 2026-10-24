import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0158
import IrregularNine14P06C0159

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r28380 : Route 9 := (fun mask => (mask,id))

def c28380 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28380 : Upper (D 6) (R 6) [6,33,72,144,260] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,260] 13 (by decide) (choices 1) [1,2,64] r28380 c28380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9506
  · exact u9507
  · exact u9508

def r28381 : Route 9 := (fun mask => (mask,id))

def c28381 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28381 : Upper (D 6) (R 6) [6,33,72,144,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,288] 13 (by decide) (choices 1) [1,2,4,64] r28381 c28381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9509
  · exact u9510
  · exact u9511
  · exact u9512

def r28382 : Route 9 := (fun mask => (mask,id))

def c28382 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28382 : Upper (D 6) (R 6) [6,33,72,144,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,320] 13 (by decide) (choices 1) [1,2,4] r28382 c28382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9513
  · exact u9514
  · exact u9515

def b28383 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 76 168 19 372 340 468 340), lower := (rows 7 35 76 168 19 32 64 128 256), losses := [] }

theorem u28383 : Upper (D 6) (R 6) [6,33,72,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28383
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28384 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 35 76 168 21 370 338 466 338), lower := (rows 7 35 76 168 21 32 64 128 256), losses := [] }

theorem u28384 : Upper (D 6) (R 6) [6,33,72,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28384
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28385 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 7 35 76 168 22 369 337 465 337), lower := (rows 7 35 76 168 22 32 64 128 256), losses := [] }

theorem u28385 : Upper (D 6) (R 6) [6,33,72,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28385
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28386 : Route 9 := (fun mask => (mask,id))

def c28386 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28386 : Upper (D 6) (R 6) [6,33,72,160,65] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,65] 13 (by decide) (choices 1) [2,4,16,256] r28386 c28386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9516
  · exact u9517
  · exact u9518
  · exact u9519

def r28387 : Route 9 := (fun mask => (mask,id))

def c28387 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28387 : Upper (D 6) (R 6) [6,33,72,160,66] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,66] 13 (by decide) (choices 1) [1,4,16,256] r28387 c28387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9520
  · exact u9521
  · exact u9522
  · exact u9523

def b28388 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 35 76 168 84 307 339 403 275), lower := (rows 7 35 76 168 84 32 64 128 256), losses := [] }

theorem u28388 : Upper (D 6) (R 6) [6,33,72,160,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28388
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28389 : Route 9 := (fun mask => (mask,id))

def c28389 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28389 : Upper (D 6) (R 6) [6,33,72,160,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,257] 13 (by decide) (choices 1) [2,4,16,64] r28389 c28389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9524
  · exact u9525
  · exact u9526
  · exact u9527

def r28390 : Route 9 := (fun mask => (mask,id))

def c28390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28390 : Upper (D 6) (R 6) [6,33,72,160,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,258] 13 (by decide) (choices 1) [1,4,16,64] r28390 c28390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9528
  · exact u9529
  · exact u9530
  · exact u9531

def r28391 : Route 9 := (fun mask => (mask,id))

def c28391 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28391 : Upper (D 6) (R 6) [6,33,72,160,260] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,260] 13 (by decide) (choices 1) [1,2,16,64] r28391 c28391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9532
  · exact u9533
  · exact u9534
  · exact u9535

def r28392 : Route 9 := (fun mask => (mask,id))

def c28392 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28392 : Upper (D 6) (R 6) [6,33,72,160,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,320] 13 (by decide) (choices 1) [1,2,4,16] r28392 c28392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9536
  · exact u9537
  · exact u9538
  · exact u9539

def b28393 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 76 392 19 116 116 244 372), lower := (rows 7 35 76 392 19 32 64 128 256), losses := [] }

theorem u28393 : Upper (D 6) (R 6) [6,33,72,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28393
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28394 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 35 76 392 21 114 114 242 370), lower := (rows 7 35 76 392 21 32 64 128 256), losses := [] }

theorem u28394 : Upper (D 6) (R 6) [6,33,72,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28394
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28395 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 35 76 392 22 113 113 241 369), lower := (rows 7 35 76 392 22 32 64 128 256), losses := [] }

theorem u28395 : Upper (D 6) (R 6) [6,33,72,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28395
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28396 : PairBound 9 := { available := 86, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 76 392 49 118 86 214 342), lower := (rows 7 35 76 392 49 32 64 128 256), losses := [] }

theorem u28396 : Upper (D 6) (R 6) [6,33,72,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28396
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28397 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 35 76 392 50 117 85 213 341), lower := (rows 7 35 76 392 50 32 64 128 256), losses := [] }

theorem u28397 : Upper (D 6) (R 6) [6,33,72,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28397
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28398 : Route 9 := (fun mask => (mask,id))

def c28398 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28398 : Upper (D 6) (R 6) [6,33,72,384,36] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,36] 13 (by decide) (choices 1) [1,2,16,64] r28398 c28398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9540
  · exact u9541
  · exact u9542
  · exact u9543

def r28399 : Route 9 := (fun mask => (mask,id))

def c28399 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28399 : Upper (D 6) (R 6) [6,33,72,384,65] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,65] 13 (by decide) (choices 1) [2,4,16] r28399 c28399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9544
  · exact u9545
  · exact u9546

def r28400 : Route 9 := (fun mask => (mask,id))

def c28400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28400 : Upper (D 6) (R 6) [6,33,72,384,66] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,66] 13 (by decide) (choices 1) [1,4,16] r28400 c28400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9547
  · exact u9548
  · exact u9549

def b28401 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 35 76 392 84 51 115 179 307), lower := (rows 7 35 76 392 84 32 64 128 256), losses := [] }

theorem u28401 : Upper (D 6) (R 6) [6,33,72,384,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28401
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28402 : Route 9 := (fun mask => (mask,id))

def c28402 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28402 : Upper (D 6) (R 6) [6,33,72,384,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,96] 13 (by decide) (choices 1) [1,2,4,16] r28402 c28402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9550
  · exact u9551
  · exact u9552
  · exact u9553

def b28403 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 368, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 133 14 56 368 336 464 336), lower := (rows 7 35 133 14 56 32 64 128 256), losses := [] }

theorem u28403 : Upper (D 6) (R 6) [6,33,129,6,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28403
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28404 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 368, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 133 14 88 368 368 496 368), lower := (rows 7 35 133 14 88 32 64 128 256), losses := [] }

theorem u28404 : Upper (D 6) (R 6) [6,33,129,6,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28404
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28405 : PairBound 9 := { available := 344, camps := [{ cop := 3, region := 368, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 133 14 112 376 344 472 344), lower := (rows 7 35 133 14 112 32 64 128 256), losses := [] }

theorem u28405 : Upper (D 6) (R 6) [6,33,129,6,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28405
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28406 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 368, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 133 14 280 112 112 240 368), lower := (rows 7 35 133 14 280 32 64 128 256), losses := [] }

theorem u28406 : Upper (D 6) (R 6) [6,33,129,6,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28406
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28407 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 368, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 133 14 304 120 88 216 344), lower := (rows 7 35 133 14 304 32 64 128 256), losses := [] }

theorem u28407 : Upper (D 6) (R 6) [6,33,129,6,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28407
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28408 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 368, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 133 14 336 120 120 248 376), lower := (rows 7 35 133 14 336 32 64 128 256), losses := [] }

theorem u28408 : Upper (D 6) (R 6) [6,33,129,6,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28408
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28409 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 133 26 28 352 352 480 352), lower := (rows 7 35 133 26 28 32 64 128 256), losses := [] }

theorem u28409 : Upper (D 6) (R 6) [6,33,129,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28409
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28410 : PairBound 9 := { available := 328, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 133 26 52 360 328 456 328), lower := (rows 7 35 133 26 52 32 64 128 256), losses := [] }

theorem u28410 : Upper (D 6) (R 6) [6,33,129,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28410
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28411 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 24, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 133 26 56 356 324 452 324), lower := (rows 7 35 133 26 56 32 64 128 256), losses := [] }

theorem u28411 : Upper (D 6) (R 6) [6,33,129,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28411
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28412 : Route 9 := (fun mask => (mask,id))

def c28412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28412 : Upper (D 6) (R 6) [6,33,129,18,68] 13 := by
  apply FastRouting.sound _ _ [6,33,129,18,68] 13 (by decide) (choices 1) [8,64,256] r28412 c28412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9554
  · exact u9555
  · exact u9556

def b28413 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 133 26 88 356 356 484 356), lower := (rows 7 35 133 26 88 32 64 128 256), losses := [] }

theorem u28413 : Upper (D 6) (R 6) [6,33,129,18,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28413
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28414 : PairBound 9 := { available := 332, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 35 133 26 112 364 332 460 332), lower := (rows 7 35 133 26 112 32 64 128 256), losses := [] }

theorem u28414 : Upper (D 6) (R 6) [6,33,129,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28414
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28415 : Route 9 := (fun mask => (mask,id))

def c28415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28415 : Upper (D 6) (R 6) [6,33,129,18,260] 13 := by
  apply FastRouting.sound _ _ [6,33,129,18,260] 13 (by decide) (choices 1) [8,64] r28415 c28415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9557
  · exact u9558

def b28416 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 133 26 280 100 100 228 356), lower := (rows 7 35 133 26 280 32 64 128 256), losses := [] }

theorem u28416 : Upper (D 6) (R 6) [6,33,129,18,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28416
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28417 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 35 133 26 304 108 76 204 332), lower := (rows 7 35 133 26 304 32 64 128 256), losses := [] }

theorem u28417 : Upper (D 6) (R 6) [6,33,129,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28417
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28418 : Route 9 := (fun mask => (mask,id))

def c28418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28418 : Upper (D 6) (R 6) [6,33,129,18,320] 13 := by
  apply FastRouting.sound _ _ [6,33,129,18,320] 13 (by decide) (choices 1) [4,8,64] r28418 c28418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9559
  · exact u9560
  · exact u9561

def b28419 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 35 133 28 50 360 328 456 328), lower := (rows 7 35 133 28 50 32 64 128 256), losses := [] }

theorem u28419 : Upper (D 6) (R 6) [6,33,129,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28419
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28420 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 35 133 28 56 354 322 450 322), lower := (rows 7 35 133 28 56 32 64 128 256), losses := [] }

theorem u28420 : Upper (D 6) (R 6) [6,33,129,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28420
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28421 : Route 9 := (fun mask => (mask,id))

def c28421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28421 : Upper (D 6) (R 6) [6,33,129,20,66] 13 := by
  apply FastRouting.sound _ _ [6,33,129,20,66] 13 (by decide) (choices 1) [8,64,256] r28421 c28421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9562
  · exact u9563
  · exact u9564

def b28422 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 354, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 133 28 88 354 354 482 354), lower := (rows 7 35 133 28 88 32 64 128 256), losses := [] }

theorem u28422 : Upper (D 6) (R 6) [6,33,129,20,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28422
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28423 : Route 9 := (fun mask => (mask,id))

def c28423 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28423 : Upper (D 6) (R 6) [6,33,129,20,96] 13 := by
  apply FastRouting.sound _ _ [6,33,129,20,96] 13 (by decide) (choices 1) [2,8,64,256] r28423 c28423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9565
  · exact u9566
  · exact u9567
  · exact u9568

def r28424 : Route 9 := (fun mask => (mask,id))

def c28424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28424 : Upper (D 6) (R 6) [6,33,129,20,258] 13 := by
  apply FastRouting.sound _ _ [6,33,129,20,258] 13 (by decide) (choices 1) [8,64] r28424 c28424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9569
  · exact u9570

def b28425 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 133 28 280 98 98 226 354), lower := (rows 7 35 133 28 280 32 64 128 256), losses := [] }

theorem u28425 : Upper (D 6) (R 6) [6,33,129,20,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28425
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28426 : Route 9 := (fun mask => (mask,id))

def c28426 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28426 : Upper (D 6) (R 6) [6,33,129,20,288] 13 := by
  apply FastRouting.sound _ _ [6,33,129,20,288] 13 (by decide) (choices 1) [2,8,64] r28426 c28426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9571
  · exact u9572
  · exact u9573

def r28427 : Route 9 := (fun mask => (mask,id))

def c28427 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28427 : Upper (D 6) (R 6) [6,33,129,20,320] 13 := by
  apply FastRouting.sound _ _ [6,33,129,20,320] 13 (by decide) (choices 1) [2,8,64] r28427 c28427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9574
  · exact u9575
  · exact u9576

def b28428 : PairBound 9 := { available := 344, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 133 42 84 376 344 472 344), lower := (rows 7 35 133 42 84 32 64 128 256), losses := [] }

theorem u28428 : Upper (D 6) (R 6) [6,33,129,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28428
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28429 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 133 42 88 372 340 468 340), lower := (rows 7 35 133 42 88 32 64 128 256), losses := [] }

theorem u28429 : Upper (D 6) (R 6) [6,33,129,34,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28429
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28430 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 133 42 276 120 88 216 344), lower := (rows 7 35 133 42 276 32 64 128 256), losses := [] }

theorem u28430 : Upper (D 6) (R 6) [6,33,129,34,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28430
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28431 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 133 42 280 116 84 212 340), lower := (rows 7 35 133 42 280 32 64 128 256), losses := [] }

theorem u28431 : Upper (D 6) (R 6) [6,33,129,34,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28431
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28432 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 133 42 336 124 92 220 348), lower := (rows 7 35 133 42 336 32 64 128 256), losses := [] }

theorem u28432 : Upper (D 6) (R 6) [6,33,129,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28432
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28433 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 133 44 82 376 344 472 344), lower := (rows 7 35 133 44 82 32 64 128 256), losses := [] }

theorem u28433 : Upper (D 6) (R 6) [6,33,129,36,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28433
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28434 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 133 44 88 370 338 466 338), lower := (rows 7 35 133 44 88 32 64 128 256), losses := [] }

theorem u28434 : Upper (D 6) (R 6) [6,33,129,36,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28434
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28435 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 133 44 274 120 88 216 344), lower := (rows 7 35 133 44 274 32 64 128 256), losses := [] }

theorem u28435 : Upper (D 6) (R 6) [6,33,129,36,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28435
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28436 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 133 44 280 114 82 210 338), lower := (rows 7 35 133 44 280 32 64 128 256), losses := [] }

theorem u28436 : Upper (D 6) (R 6) [6,33,129,36,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28436
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28437 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 133 44 336 122 90 218 346), lower := (rows 7 35 133 44 336 32 64 128 256), losses := [] }

theorem u28437 : Upper (D 6) (R 6) [6,33,129,36,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28437
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28438 : Route 9 := (fun mask => (mask,id))

def c28438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28438 : Upper (D 6) (R 6) [6,33,129,48,66] 13 := by
  apply FastRouting.sound _ _ [6,33,129,48,66] 13 (by decide) (choices 1) [4,8,64,256] r28438 c28438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9577
  · exact u9578
  · exact u9579
  · exact u9580

def r28439 : Route 9 := (fun mask => (mask,id))

def c28439 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28439 : Upper (D 6) (R 6) [6,33,129,48,68] 13 := by
  apply FastRouting.sound _ _ [6,33,129,48,68] 13 (by decide) (choices 1) [2,8,64,256] r28439 c28439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9581
  · exact u9582
  · exact u9583
  · exact u9584

#print axioms u28439
end Delivery.IrregularNine14.P06
