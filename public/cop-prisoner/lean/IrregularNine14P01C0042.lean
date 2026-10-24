import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0009

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2520 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 51 67 28 168 272 230 198 198 454), lower := (rows 51 67 28 168 272 32 64 128 256), losses := [] }

theorem u2520 : Upper (D 1) (R 1) [50,65,24,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2520
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2521 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 28 200 18 420 484 420 420), lower := (rows 51 67 28 200 18 32 64 128 256), losses := [] }

theorem u2521 : Upper (D 1) (R 1) [50,65,24,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2521
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2522 : PairBound 9 := { available := 418, camps := [], pairs := [], upper := (rows 51 67 28 200 20 418 482 418 418), lower := (rows 51 67 28 200 20 32 64 128 256), losses := [] }

theorem u2522 : Upper (D 1) (R 1) [50,65,24,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2522
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2523 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 28 200 48 422 454 390 390), lower := (rows 51 67 28 200 48 32 64 128 256), losses := [] }

theorem u2523 : Upper (D 1) (R 1) [50,65,24,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2523
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2524 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 28 200 144 294 358 422 294), lower := (rows 51 67 28 200 144 32 64 128 256), losses := [] }

theorem u2524 : Upper (D 1) (R 1) [50,65,24,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2524
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2525 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 51 67 28 200 272 166 230 166 422), lower := (rows 51 67 28 200 272 32 64 128 256), losses := [] }

theorem u2525 : Upper (D 1) (R 1) [50,65,24,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2525
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2526 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 28 296 18 228 196 196 452), lower := (rows 51 67 28 296 18 32 64 128 256), losses := [] }

theorem u2526 : Upper (D 1) (R 1) [50,65,24,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2526
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2527 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 51 67 28 296 20 226 194 194 450), lower := (rows 51 67 28 296 20 32 64 128 256), losses := [] }

theorem u2527 : Upper (D 1) (R 1) [50,65,24,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2527
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2528 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 28 296 80 166 198 134 390), lower := (rows 51 67 28 296 80 32 64 128 256), losses := [] }

theorem u2528 : Upper (D 1) (R 1) [50,65,24,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2528
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2529 : Route 9 := (fun mask => (mask,id))

def c2529 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2529 : Upper (D 1) (R 1) [50,65,24,288,128] 13 := by
  apply FastRouting.sound _ _ [50,65,24,288,128] 13 (by decide) (choices 1) [2,4,64,128] r2529 c2529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u558
  · exact u559
  · exact u560
  · exact u561

def b2530 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 28 328 18 164 228 164 420), lower := (rows 51 67 28 328 18 32 64 128 256), losses := [] }

theorem u2530 : Upper (D 1) (R 1) [50,65,24,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2530
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2531 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 51 67 28 328 20 162 226 162 418), lower := (rows 51 67 28 328 20 32 64 128 256), losses := [] }

theorem u2531 : Upper (D 1) (R 1) [50,65,24,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2531
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2532 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 28 328 48 166 198 134 390), lower := (rows 51 67 28 328 48 32 64 128 256), losses := [] }

theorem u2532 : Upper (D 1) (R 1) [50,65,24,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2532
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2533 : Route 9 := (fun mask => (mask,id))

def c2533 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2533 : Upper (D 1) (R 1) [50,65,24,320,128] 13 := by
  apply FastRouting.sound _ _ [50,65,24,320,128] 13 (by decide) (choices 1) [2,4,128] r2533 c2533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u562
  · exact u563
  · exact u564

def b2534 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 28 392 18 228 228 228 484), lower := (rows 51 67 28 392 18 32 64 128 256), losses := [] }

theorem u2534 : Upper (D 1) (R 1) [50,65,24,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2534
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2535 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 51 67 28 392 20 226 226 226 482), lower := (rows 51 67 28 392 20 32 64 128 256), losses := [] }

theorem u2535 : Upper (D 1) (R 1) [50,65,24,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2535
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2536 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 28 392 48 230 198 198 454), lower := (rows 51 67 28 392 48 32 64 128 256), losses := [] }

theorem u2536 : Upper (D 1) (R 1) [50,65,24,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2536
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2537 : PairBound 9 := { available := 166, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 28 392 80 166 230 166 422), lower := (rows 51 67 28 392 80 32 64 128 256), losses := [] }

theorem u2537 : Upper (D 1) (R 1) [50,65,24,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2537
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2538 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 28 392 144 102 102 230 358), lower := (rows 51 67 28 392 144 32 64 128 256), losses := [] }

theorem u2538 : Upper (D 1) (R 1) [50,65,24,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2538
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2539 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 76 152 18 420 484 420 420), lower := (rows 51 67 76 152 18 32 64 128 256), losses := [] }

theorem u2539 : Upper (D 1) (R 1) [50,65,72,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2539
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2540 : PairBound 9 := { available := 418, camps := [], pairs := [], upper := (rows 51 67 76 152 20 418 482 418 418), lower := (rows 51 67 76 152 20 32 64 128 256), losses := [] }

theorem u2540 : Upper (D 1) (R 1) [50,65,72,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2540
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2541 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 76 152 48 422 454 390 390), lower := (rows 51 67 76 152 48 32 64 128 256), losses := [] }

theorem u2541 : Upper (D 1) (R 1) [50,65,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2541
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2542 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 67 76 152 144 294 358 422 294), lower := (rows 51 67 76 152 144 32 64 128 256), losses := [] }

theorem u2542 : Upper (D 1) (R 1) [50,65,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2542
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2543 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 51 67 76 152 272 166 230 166 422), lower := (rows 51 67 76 152 272 32 64 128 256), losses := [] }

theorem u2543 : Upper (D 1) (R 1) [50,65,72,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2543
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2544 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 76 280 18 164 228 164 420), lower := (rows 51 67 76 280 18 32 64 128 256), losses := [] }

theorem u2544 : Upper (D 1) (R 1) [50,65,72,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2544
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2545 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 51 67 76 280 20 162 226 162 418), lower := (rows 51 67 76 280 20 32 64 128 256), losses := [] }

theorem u2545 : Upper (D 1) (R 1) [50,65,72,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2545
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2546 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 76 280 48 166 198 134 390), lower := (rows 51 67 76 280 48 32 64 128 256), losses := [] }

theorem u2546 : Upper (D 1) (R 1) [50,65,72,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2546
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2547 : Route 9 := (fun mask => (mask,id))

def c2547 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2547 : Upper (D 1) (R 1) [50,65,72,272,128] 13 := by
  apply FastRouting.sound _ _ [50,65,72,272,128] 13 (by decide) (choices 1) [2,4,128] r2547 c2547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u565
  · exact u566
  · exact u567

def b2548 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 76 392 18 180 244 180 436), lower := (rows 51 67 76 392 18 32 64 128 256), losses := [] }

theorem u2548 : Upper (D 1) (R 1) [50,65,72,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2548
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2549 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 67 76 392 20 178 242 178 434), lower := (rows 51 67 76 392 20 32 64 128 256), losses := [] }

theorem u2549 : Upper (D 1) (R 1) [50,65,72,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2549
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2550 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 76 392 48 182 214 150 406), lower := (rows 51 67 76 392 48 32 64 128 256), losses := [] }

theorem u2550 : Upper (D 1) (R 1) [50,65,72,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2550
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2551_2 : Upper (D 1) (R 1) [50,65,72,384,128,2] 13 :=
  permutation_upper _ _ _ [50,65,72,384,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u568

theorem m2551_4 : Upper (D 1) (R 1) [50,65,72,384,128,4] 13 :=
  permutation_upper _ _ _ [50,65,72,384,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u569

theorem m2551_16 : Upper (D 1) (R 1) [50,65,72,384,128,16] 13 :=
  permutation_upper _ _ _ [50,65,72,384,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u570

def r2551 : Route 9 := (fun mask => (mask,id))

def c2551 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2551 : Upper (D 1) (R 1) [50,65,72,384,128] 13 := by
  apply FastRouting.sound _ _ [50,65,72,384,128] 13 (by decide) (choices 1) [2,4,16] r2551 c2551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2551_2
  · exact m2551_4
  · exact m2551_16

def b2552 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 84 140 18 424 488 424 424), lower := (rows 51 67 84 140 18 32 64 128 256), losses := [] }

theorem u2552 : Upper (D 1) (R 1) [50,65,80,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2552
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2553 : PairBound 9 := { available := 418, camps := [], pairs := [], upper := (rows 51 67 84 140 24 418 482 418 418), lower := (rows 51 67 84 140 24 32 64 128 256), losses := [] }

theorem u2553 : Upper (D 1) (R 1) [50,65,80,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2553
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2554 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 84 140 48 426 458 394 394), lower := (rows 51 67 84 140 48 32 64 128 256), losses := [] }

theorem u2554 : Upper (D 1) (R 1) [50,65,80,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2554
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2555 : Route 9 := (fun mask => (mask,id))

def c2555 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2555 : Upper (D 1) (R 1) [50,65,80,132,128] 13 := by
  apply FastRouting.sound _ _ [50,65,80,132,128] 13 (by decide) (choices 1) [2,8,256] r2555 c2555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u571
  · exact u572
  · exact u573

def b2556 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 67 84 140 272 170 234 170 426), lower := (rows 51 67 84 140 272 32 64 128 256), losses := [] }

theorem u2556 : Upper (D 1) (R 1) [50,65,80,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2556
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2557 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 84 168 18 428 460 396 396), lower := (rows 51 67 84 168 18 32 64 128 256), losses := [] }

theorem u2557 : Upper (D 1) (R 1) [50,65,80,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2557
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2558 : PairBound 9 := { available := 394, camps := [], pairs := [], upper := (rows 51 67 84 168 20 426 458 394 394), lower := (rows 51 67 84 168 20 32 64 128 256), losses := [] }

theorem u2558 : Upper (D 1) (R 1) [50,65,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2558
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2559 : PairBound 9 := { available := 390, camps := [], pairs := [], upper := (rows 51 67 84 168 24 422 454 390 390), lower := (rows 51 67 84 168 24 32 64 128 256), losses := [] }

theorem u2559 : Upper (D 1) (R 1) [50,65,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2559
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2560 : Route 9 := (fun mask => (mask,id))

def c2560 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2560 : Upper (D 1) (R 1) [50,65,80,160,128] 13 := by
  apply FastRouting.sound _ _ [50,65,80,160,128] 13 (by decide) (choices 1) [2,4,8,256] r2560 c2560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u574
  · exact u575
  · exact u576
  · exact u577

def b2561 : PairBound 9 := { available := 142, camps := [], pairs := [], upper := (rows 51 67 84 168 272 174 206 142 398), lower := (rows 51 67 84 168 272 32 64 128 256), losses := [] }

theorem u2561 : Upper (D 1) (R 1) [50,65,80,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2561
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2562 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 84 268 18 168 232 168 424), lower := (rows 51 67 84 268 18 32 64 128 256), losses := [] }

theorem u2562 : Upper (D 1) (R 1) [50,65,80,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2562
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2563 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 51 67 84 268 24 162 226 162 418), lower := (rows 51 67 84 268 24 32 64 128 256), losses := [] }

theorem u2563 : Upper (D 1) (R 1) [50,65,80,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2563
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2564 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 84 268 48 170 202 138 394), lower := (rows 51 67 84 268 48 32 64 128 256), losses := [] }

theorem u2564 : Upper (D 1) (R 1) [50,65,80,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2564
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2565 : Route 9 := (fun mask => (mask,id))

def c2565 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2565 : Upper (D 1) (R 1) [50,65,80,260,128] 13 := by
  apply FastRouting.sound _ _ [50,65,80,260,128] 13 (by decide) (choices 1) [2,8,128] r2565 c2565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u578
  · exact u579
  · exact u580

def b2566 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 84 296 18 172 204 140 396), lower := (rows 51 67 84 296 18 32 64 128 256), losses := [] }

theorem u2566 : Upper (D 1) (R 1) [50,65,80,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2566
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2567 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 51 67 84 296 20 170 202 138 394), lower := (rows 51 67 84 296 20 32 64 128 256), losses := [] }

theorem u2567 : Upper (D 1) (R 1) [50,65,80,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2567
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2568 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 51 67 84 296 24 166 198 134 390), lower := (rows 51 67 84 296 24 32 64 128 256), losses := [] }

theorem u2568 : Upper (D 1) (R 1) [50,65,80,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2568
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2569 : Route 9 := (fun mask => (mask,id))

def c2569 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2569 : Upper (D 1) (R 1) [50,65,80,288,128] 13 := by
  apply FastRouting.sound _ _ [50,65,80,288,128] 13 (by decide) (choices 1) [2,4,8,128] r2569 c2569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u581
  · exact u582
  · exact u583
  · exact u584

def b2570 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 84 392 18 172 236 172 428), lower := (rows 51 67 84 392 18 32 64 128 256), losses := [] }

theorem u2570 : Upper (D 1) (R 1) [50,65,80,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2570
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2571 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 67 84 392 20 170 234 170 426), lower := (rows 51 67 84 392 20 32 64 128 256), losses := [] }

theorem u2571 : Upper (D 1) (R 1) [50,65,80,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2571
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2572 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 51 67 84 392 24 166 230 166 422), lower := (rows 51 67 84 392 24 32 64 128 256), losses := [] }

theorem u2572 : Upper (D 1) (R 1) [50,65,80,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2572
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2573 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 84 392 48 174 206 142 398), lower := (rows 51 67 84 392 48 32 64 128 256), losses := [] }

theorem u2573 : Upper (D 1) (R 1) [50,65,80,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2573
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2574 : Route 9 := (fun mask => (mask,id))

def c2574 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2574 : Upper (D 1) (R 1) [50,65,80,384,128] 13 := by
  apply FastRouting.sound _ _ [50,65,80,384,128] 13 (by decide) (choices 1) [2,4,8] r2574 c2574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u585
  · exact u586
  · exact u587

def b2575 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 140 268 18 240 240 240 496), lower := (rows 51 67 140 268 18 32 64 128 256), losses := [] }

theorem u2575 : Upper (D 1) (R 1) [50,65,136,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2575
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2576 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 140 268 48 242 210 210 466), lower := (rows 51 67 140 268 48 32 64 128 256), losses := [] }

theorem u2576 : Upper (D 1) (R 1) [50,65,136,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2576
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2577 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 140 268 80 178 242 178 434), lower := (rows 51 67 140 268 80 32 64 128 256), losses := [] }

theorem u2577 : Upper (D 1) (R 1) [50,65,136,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2577
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2578 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 51 67 140 268 144 114 114 242 370), lower := (rows 51 67 140 268 144 32 64 128 256), losses := [] }

theorem u2578 : Upper (D 1) (R 1) [50,65,136,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2578
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2579 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 140 280 18 228 228 228 484), lower := (rows 51 67 140 280 18 32 64 128 256), losses := [] }

theorem u2579 : Upper (D 1) (R 1) [50,65,136,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2579
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2579
end Delivery.IrregularNine14.P01
