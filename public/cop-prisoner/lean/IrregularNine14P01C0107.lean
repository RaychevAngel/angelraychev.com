import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0042
import IrregularNine14P01C0043
import IrregularNine14P01C0044

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6420 : PairBound 9 := { available := 316, camps := [{ cop := 2, region := 376, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 134 200 316 316 380 444 316), lower := (rows 51 67 134 200 16 32 64 128 256), losses := [] }

theorem u6420 : Upper (D 1) (R 1) [50,65,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6420
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6421 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 376, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 134 268 248 248 248 248 504), lower := (rows 51 67 134 268 16 32 64 128 256), losses := [] }

theorem u6421 : Upper (D 1) (R 1) [50,65,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6421
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6422 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 376, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 134 280 252 236 236 236 492), lower := (rows 51 67 134 280 16 32 64 128 256), losses := [] }

theorem u6422 : Upper (D 1) (R 1) [50,65,130,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6422
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6423 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 376, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 134 328 188 188 252 188 444), lower := (rows 51 67 134 328 16 32 64 128 256), losses := [] }

theorem u6423 : Upper (D 1) (R 1) [50,65,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6423
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6424 : PairBound 9 := { available := 124, camps := [{ cop := 2, region := 376, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 134 392 124 124 124 252 380), lower := (rows 51 67 134 392 16 32 64 128 256), losses := [] }

theorem u6424 : Upper (D 1) (R 1) [50,65,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6424
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6425 : PairBound 9 := { available := 370, camps := [{ cop := 7, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 140 140 370 370 370 498 370), lower := (rows 51 67 140 140 16 32 64 128 256), losses := [] }

theorem u6425 : Upper (D 1) (R 1) [50,65,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6425
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6426 : PairBound 9 := { available := 358, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 140 152 374 358 358 486 358), lower := (rows 51 67 140 152 16 32 64 128 256), losses := [] }

theorem u6426 : Upper (D 1) (R 1) [50,65,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6426
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6427 : PairBound 9 := { available := 310, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 140 200 310 310 374 438 310), lower := (rows 51 67 140 200 16 32 64 128 256), losses := [] }

theorem u6427 : Upper (D 1) (R 1) [50,65,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6427
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6428 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 140 266 244 244 244 244 500), lower := (rows 51 67 140 266 16 32 64 128 256), losses := [] }

theorem u6428 : Upper (D 1) (R 1) [50,65,136,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6428
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6429 : Route 9 := (fun mask => (mask,id))

def c6429 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6429 : Upper (D 1) (R 1) [50,65,136,260] 13 := by
  apply FastRouting.sound _ _ [50,65,136,260] 13 (by decide) (choices 1) [2,32,64,128] r6429 c6429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2575
  · exact u2576
  · exact u2577
  · exact u2578

def r6430 : Route 9 := (fun mask => (mask,id))

def c6430 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u6430 : Upper (D 1) (R 1) [50,65,136,272] 13 := by
  apply FastRouting.sound _ _ [50,65,136,272] 13 (by decide) (choices 1) [2,4,32,64,128] r6430 c6430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2579
  · exact u2580
  · exact u2581
  · exact u2582
  · exact u2583

def r6431 : Route 9 := (fun mask => (mask,id))

def c6431 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6431 : Upper (D 1) (R 1) [50,65,136,320] 13 := by
  apply FastRouting.sound _ _ [50,65,136,320] 13 (by decide) (choices 1) [2,4,32,128] r6431 c6431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2584
  · exact u2585
  · exact u2586
  · exact u2587

def b6432 : PairBound 9 := { available := 118, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 140 392 118 118 118 246 374), lower := (rows 51 67 140 392 16 32 64 128 256), losses := [] }

theorem u6432 : Upper (D 1) (R 1) [50,65,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6432
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6433 : Route 9 := (fun mask => (mask,id))

def c6433 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | _ => 0)

theorem u6433 : Upper (D 1) (R 1) [50,65,144,160] 13 := by
  apply FastRouting.sound _ _ [50,65,144,160] 13 (by decide) (choices 1) [2,4,8,64,256] r6433 c6433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2588
  · exact u2589
  · exact u2590
  · exact u2591
  · exact u2592

def r6434 : Route 9 := (fun mask => (mask,id))

def c6434 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | _ => 0)

theorem u6434 : Upper (D 1) (R 1) [50,65,144,192] 13 := by
  apply FastRouting.sound _ _ [50,65,144,192] 13 (by decide) (choices 1) [2,4,8,32,256] r6434 c6434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2593
  · exact u2594
  · exact u2595
  · exact u2596
  · exact u2597

def b6435 : PairBound 9 := { available := 236, camps := [{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 148 266 252 236 236 236 492), lower := (rows 51 67 148 266 16 32 64 128 256), losses := [] }

theorem u6435 : Upper (D 1) (R 1) [50,65,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6435
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6436 : Route 9 := (fun mask => (mask,id))

def c6436 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u6436 : Upper (D 1) (R 1) [50,65,144,260] 13 := by
  apply FastRouting.sound _ _ [50,65,144,260] 13 (by decide) (choices 1) [2,8,32,64,128] r6436 c6436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2598
  · exact u2599
  · exact u2600
  · exact u2601
  · exact u2602

def r6437 : Route 9 := (fun mask => (mask,id))

def c6437 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 256 => 8 | _ => 0)

theorem u6437 : Upper (D 1) (R 1) [50,65,144,288] 13 := by
  apply FastRouting.sound _ _ [50,65,144,288] 13 (by decide) (choices 1) [2,4,8,64,128] r6437 c6437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2603
  · exact u2604
  · exact u2605
  · exact u2606
  · exact u2607

def r6438 : Route 9 := (fun mask => (mask,id))

def c6438 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 256 => 8 | _ => 0)

theorem u6438 : Upper (D 1) (R 1) [50,65,144,320] 13 := by
  apply FastRouting.sound _ _ [50,65,144,320] 13 (by decide) (choices 1) [2,4,8,32,128] r6438 c6438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2608
  · exact u2609
  · exact u2610
  · exact u2611
  · exact u2612

def r6439 : Route 9 := (fun mask => (mask,id))

def c6439 : Nat → Fin 9 := (fun mask => match mask with | 128 => 7 | 256 => 8 | _ => 0)

theorem u6439 : Upper (D 1) (R 1) [50,65,144,384] 13 := by
  apply FastRouting.sound _ _ [50,65,144,384] 13 (by decide) (choices 1) [2,4,8,32,64] r6439 c6439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2613
  · exact u2614
  · exact u2615
  · exact u2616
  · exact u2617

def b6440 : PairBound 9 := { available := 188, camps := [{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 196 266 188 188 252 188 444), lower := (rows 51 67 196 266 16 32 64 128 256), losses := [] }

theorem u6440 : Upper (D 1) (R 1) [50,65,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6440
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6441 : Route 9 := (fun mask => (mask,id))

def c6441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6441 : Upper (D 1) (R 1) [50,65,192,260] 13 := by
  apply FastRouting.sound _ _ [50,65,192,260] 13 (by decide) (choices 1) [2,8,32,128] r6441 c6441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2618
  · exact u2619
  · exact u2620
  · exact u2621

def r6442 : Route 9 := (fun mask => (mask,id))

def c6442 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 256 => 8 | _ => 0)

theorem u6442 : Upper (D 1) (R 1) [50,65,192,272] 13 := by
  apply FastRouting.sound _ _ [50,65,192,272] 13 (by decide) (choices 1) [2,4,8,32,128] r6442 c6442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2622
  · exact u2623
  · exact u2624
  · exact u2625
  · exact u2626

def r6443 : Route 9 := (fun mask => (mask,id))

def c6443 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6443 : Upper (D 1) (R 1) [50,65,192,384] 13 := by
  apply FastRouting.sound _ _ [50,65,192,384] 13 (by decide) (choices 1) [2,4,8,32] r6443 c6443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2627
  · exact u2628
  · exact u2629
  · exact u2630

def b6444 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 70 13 26 496 480 480 480 480), lower := (rows 51 70 13 26 16 32 64 128 256), losses := [] }

theorem u6444 : Upper (D 1) (R 1) [50,68,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6444
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6445 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 13 56 466 482 450 450 450), lower := (rows 51 70 13 56 16 32 64 128 256), losses := [] }

theorem u6445 : Upper (D 1) (R 1) [50,68,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6445
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6446 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 13 74 432 432 496 432 432), lower := (rows 51 70 13 74 16 32 64 128 256), losses := [] }

theorem u6446 : Upper (D 1) (R 1) [50,68,9,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6446
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6447 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 13 88 434 418 482 418 418), lower := (rows 51 70 13 88 16 32 64 128 256), losses := [] }

theorem u6447 : Upper (D 1) (R 1) [50,68,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6447
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6448 : Route 9 := (fun mask => (mask,id))

def c6448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u6448 : Upper (D 1) (R 1) [50,68,9,130] 13 := by
  apply FastRouting.sound _ _ [50,68,9,130] 13 (by decide) (choices 1) [32,64,128,256] r6448 c6448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2631
  · exact u2632
  · exact u2633
  · exact u2634

def b6449 : PairBound 9 := { available := 482, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 13 152 498 482 482 482 482), lower := (rows 51 70 13 152 16 32 64 128 256), losses := [] }

theorem u6449 : Upper (D 1) (R 1) [50,68,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6449
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6450 : PairBound 9 := { available := 434, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 13 200 434 434 498 434 434), lower := (rows 51 70 13 200 16 32 64 128 256), losses := [] }

theorem u6450 : Upper (D 1) (R 1) [50,68,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6450
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6451 : Route 9 := (fun mask => (mask,id))

def c6451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6451 : Upper (D 1) (R 1) [50,68,9,258] 13 := by
  apply FastRouting.sound _ _ [50,68,9,258] 13 (by decide) (choices 1) [32,64,128] r6451 c6451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2635
  · exact u2636
  · exact u2637

def b6452 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 13 280 242 226 226 226 482), lower := (rows 51 70 13 280 16 32 64 128 256), losses := [] }

theorem u6452 : Upper (D 1) (R 1) [50,68,9,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6452
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6453 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 13 328 178 178 242 178 434), lower := (rows 51 70 13 328 16 32 64 128 256), losses := [] }

theorem u6453 : Upper (D 1) (R 1) [50,68,9,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6453
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6454 : Route 9 := (fun mask => (mask,id))

def c6454 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6454 : Upper (D 1) (R 1) [50,68,9,384] 13 := by
  apply FastRouting.sound _ _ [50,68,9,384] 13 (by decide) (choices 1) [2,32,64,128] r6454 c6454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2638
  · exact u2639
  · exact u2640
  · exact u2641

def b6455 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 133 26 504 488 488 488 488), lower := (rows 51 70 133 26 16 32 64 128 256), losses := [] }

theorem u6455 : Upper (D 1) (R 1) [50,68,129,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6455
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6456 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 70 133 56 474 490 458 458 458), lower := (rows 51 70 133 56 16 32 64 128 256), losses := [] }

theorem u6456 : Upper (D 1) (R 1) [50,68,129,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6456
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6457 : PairBound 9 := { available := 440, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 133 74 440 440 504 440 440), lower := (rows 51 70 133 74 16 32 64 128 256), losses := [] }

theorem u6457 : Upper (D 1) (R 1) [50,68,129,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6457
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6458 : Route 9 := (fun mask => (mask,id))

def c6458 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | _ => 0)

theorem u6458 : Upper (D 1) (R 1) [50,68,129,80] 13 := by
  apply FastRouting.sound _ _ [50,68,129,80] 13 (by decide) (choices 1) [2,8,32,128,256] r6458 c6458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2642
  · exact u2643
  · exact u2644
  · exact u2645
  · exact u2646

def b6459 : PairBound 9 := { available := 376, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 51 70 133 138 376 376 376 504 376), lower := (rows 51 70 133 138 16 32 64 128 256), losses := [] }

theorem u6459 : Upper (D 1) (R 1) [50,68,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6459
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6460 : Route 9 := (fun mask => (mask,id))

def c6460 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | _ => 0)

theorem u6460 : Upper (D 1) (R 1) [50,68,129,144] 13 := by
  apply FastRouting.sound _ _ [50,68,129,144] 13 (by decide) (choices 1) [2,8,32,64,256] r6460 c6460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2647
  · exact u2648
  · exact u2649
  · exact u2650
  · exact u2651

def r6461 : Route 9 := (fun mask => (mask,id))

def c6461 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6461 : Upper (D 1) (R 1) [50,68,129,192] 13 := by
  apply FastRouting.sound _ _ [50,68,129,192] 13 (by decide) (choices 1) [2,8,32,256] r6461 c6461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2652
  · exact u2653
  · exact u2654
  · exact u2655

def r6462 : Route 9 := (fun mask => (mask,id))

def c6462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u6462 : Upper (D 1) (R 1) [50,68,129,258] 13 := by
  apply FastRouting.sound _ _ [50,68,129,258] 13 (by decide) (choices 1) [8,32,64,128] r6462 c6462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2656
  · exact u2657
  · exact u2658
  · exact u2659

def r6463 : Route 9 := (fun mask => (mask,id))

def c6463 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u6463 : Upper (D 1) (R 1) [50,68,129,272] 13 := by
  apply FastRouting.sound _ _ [50,68,129,272] 13 (by decide) (choices 1) [2,8,32,64,128] r6463 c6463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2660
  · exact u2661
  · exact u2662
  · exact u2663
  · exact u2664

def r6464 : Route 9 := (fun mask => (mask,id))

def c6464 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6464 : Upper (D 1) (R 1) [50,68,129,320] 13 := by
  apply FastRouting.sound _ _ [50,68,129,320] 13 (by decide) (choices 1) [2,8,32,128] r6464 c6464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2665
  · exact u2666
  · exact u2667
  · exact u2668

def r6465 : Route 9 := (fun mask => (mask,id))

def c6465 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6465 : Upper (D 1) (R 1) [50,68,129,384] 13 := by
  apply FastRouting.sound _ _ [50,68,129,384] 13 (by decide) (choices 1) [2,8,32,64] r6465 c6465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2669
  · exact u2670
  · exact u2671
  · exact u2672

def b6466 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 140 11 496 496 496 496 496), lower := (rows 51 70 140 11 16 32 64 128 256), losses := [] }

theorem u6466 : Upper (D 1) (R 1) [50,68,136,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6466
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6467 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 70 140 25 498 482 482 482 482), lower := (rows 51 70 140 25 16 32 64 128 256), losses := [] }

theorem u6467 : Upper (D 1) (R 1) [50,68,136,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6467
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6468 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 140 26 497 481 481 481 481), lower := (rows 51 70 140 26 16 32 64 128 256), losses := [] }

theorem u6468 : Upper (D 1) (R 1) [50,68,136,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6468
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6469 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 70 140 56 467 483 451 451 451), lower := (rows 51 70 140 56 16 32 64 128 256), losses := [] }

theorem u6469 : Upper (D 1) (R 1) [50,68,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6469
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6470 : PairBound 9 := { available := 434, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 140 73 434 434 498 434 434), lower := (rows 51 70 140 73 16 32 64 128 256), losses := [] }

theorem u6470 : Upper (D 1) (R 1) [50,68,136,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6470
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6471 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 140 74 433 433 497 433 433), lower := (rows 51 70 140 74 16 32 64 128 256), losses := [] }

theorem u6471 : Upper (D 1) (R 1) [50,68,136,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6471
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6472 : PairBound 9 := { available := 419, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 140 88 435 419 483 419 419), lower := (rows 51 70 140 88 16 32 64 128 256), losses := [] }

theorem u6472 : Upper (D 1) (R 1) [50,68,136,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6472
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6473 : PairBound 9 := { available := 370, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 140 137 370 370 370 498 370), lower := (rows 51 70 140 137 16 32 64 128 256), losses := [] }

theorem u6473 : Upper (D 1) (R 1) [50,68,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6473
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6474 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 140 138 369 369 369 497 369), lower := (rows 51 70 140 138 16 32 64 128 256), losses := [] }

theorem u6474 : Upper (D 1) (R 1) [50,68,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6474
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6475 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 140 152 371 355 355 483 355), lower := (rows 51 70 140 152 16 32 64 128 256), losses := [] }

theorem u6475 : Upper (D 1) (R 1) [50,68,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6475
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6476 : PairBound 9 := { available := 307, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 140 200 307 307 371 435 307), lower := (rows 51 70 140 200 16 32 64 128 256), losses := [] }

theorem u6476 : Upper (D 1) (R 1) [50,68,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6476
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6477 : Route 9 := (fun mask => (mask,id))

def c6477 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6477 : Upper (D 1) (R 1) [50,68,136,257] 13 := by
  apply FastRouting.sound _ _ [50,68,136,257] 13 (by decide) (choices 1) [2,32,64,128] r6477 c6477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2673
  · exact u2674
  · exact u2675
  · exact u2676

def r6478 : Route 9 := (fun mask => (mask,id))

def c6478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6478 : Upper (D 1) (R 1) [50,68,136,258] 13 := by
  apply FastRouting.sound _ _ [50,68,136,258] 13 (by decide) (choices 1) [1,32,64,128] r6478 c6478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2677
  · exact u2678
  · exact u2679
  · exact u2680

def r6479 : Route 9 := (fun mask => (mask,id))

def c6479 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6479 : Upper (D 1) (R 1) [50,68,136,272] 13 := by
  apply FastRouting.sound _ _ [50,68,136,272] 13 (by decide) (choices 1) [1,2,32,64,128] r6479 c6479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2681
  · exact u2682
  · exact u2683
  · exact u2684
  · exact u2685

#print axioms u6479
end Delivery.IrregularNine14.P01
