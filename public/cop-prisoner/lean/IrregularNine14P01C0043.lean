import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0009
import IrregularNine14P01C0010

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2580 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 51 67 140 280 20 226 226 226 482), lower := (rows 51 67 140 280 20 32 64 128 256), losses := [] }

theorem u2580 : Upper (D 1) (R 1) [50,65,136,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2580
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2581 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 140 280 48 230 198 198 454), lower := (rows 51 67 140 280 48 32 64 128 256), losses := [] }

theorem u2581 : Upper (D 1) (R 1) [50,65,136,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2581
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2582 : PairBound 9 := { available := 166, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 140 280 80 166 230 166 422), lower := (rows 51 67 140 280 80 32 64 128 256), losses := [] }

theorem u2582 : Upper (D 1) (R 1) [50,65,136,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2582
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2583 : Route 9 := (fun mask => (mask,id))

def c2583 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2583 : Upper (D 1) (R 1) [50,65,136,272,128] 13 := by
  apply FastRouting.sound _ _ [50,65,136,272,128] 13 (by decide) (choices 1) [2,4,64] r2583 c2583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u588
  · exact u589
  · exact u590

def b2584 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 140 328 18 180 244 180 436), lower := (rows 51 67 140 328 18 32 64 128 256), losses := [] }

theorem u2584 : Upper (D 1) (R 1) [50,65,136,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2584
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2585 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 67 140 328 20 178 242 178 434), lower := (rows 51 67 140 328 20 32 64 128 256), losses := [] }

theorem u2585 : Upper (D 1) (R 1) [50,65,136,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2585
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2586 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 140 328 48 182 214 150 406), lower := (rows 51 67 140 328 48 32 64 128 256), losses := [] }

theorem u2586 : Upper (D 1) (R 1) [50,65,136,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2586
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2587_2 : Upper (D 1) (R 1) [50,65,136,320,128,2] 13 :=
  permutation_upper _ _ _ [50,65,136,320,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u591

theorem m2587_4 : Upper (D 1) (R 1) [50,65,136,320,128,4] 13 :=
  permutation_upper _ _ _ [50,65,136,320,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u592

theorem m2587_16 : Upper (D 1) (R 1) [50,65,136,320,128,16] 13 :=
  permutation_upper _ _ _ [50,65,136,320,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u593

def r2587 : Route 9 := (fun mask => (mask,id))

def c2587 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2587 : Upper (D 1) (R 1) [50,65,136,320,128] 13 := by
  apply FastRouting.sound _ _ [50,65,136,320,128] 13 (by decide) (choices 1) [2,4,16] r2587 c2587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2587_2
  · exact m2587_4
  · exact m2587_16

def b2588 : PairBound 9 := { available := 332, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 148 168 18 364 332 460 332), lower := (rows 51 67 148 168 18 32 64 128 256), losses := [] }

theorem u2588 : Upper (D 1) (R 1) [50,65,144,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2588
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2589 : PairBound 9 := { available := 330, camps := [], pairs := [], upper := (rows 51 67 148 168 20 362 330 458 330), lower := (rows 51 67 148 168 20 32 64 128 256), losses := [] }

theorem u2589 : Upper (D 1) (R 1) [50,65,144,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2589
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2590 : PairBound 9 := { available := 326, camps := [], pairs := [], upper := (rows 51 67 148 168 24 358 326 454 326), lower := (rows 51 67 148 168 24 32 64 128 256), losses := [] }

theorem u2590 : Upper (D 1) (R 1) [50,65,144,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2590
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2591 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 148 168 80 302 334 398 270), lower := (rows 51 67 148 168 80 32 64 128 256), losses := [] }

theorem u2591 : Upper (D 1) (R 1) [50,65,144,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2591
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2592 : PairBound 9 := { available := 78, camps := [], pairs := [], upper := (rows 51 67 148 168 272 110 78 206 334), lower := (rows 51 67 148 168 272 32 64 128 256), losses := [] }

theorem u2592 : Upper (D 1) (R 1) [50,65,144,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2592
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2593 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 148 200 18 300 364 428 300), lower := (rows 51 67 148 200 18 32 64 128 256), losses := [] }

theorem u2593 : Upper (D 1) (R 1) [50,65,144,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2593
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2594 : PairBound 9 := { available := 298, camps := [], pairs := [], upper := (rows 51 67 148 200 20 298 362 426 298), lower := (rows 51 67 148 200 20 32 64 128 256), losses := [] }

theorem u2594 : Upper (D 1) (R 1) [50,65,144,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2594
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2595 : PairBound 9 := { available := 294, camps := [], pairs := [], upper := (rows 51 67 148 200 24 294 358 422 294), lower := (rows 51 67 148 200 24 32 64 128 256), losses := [] }

theorem u2595 : Upper (D 1) (R 1) [50,65,144,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2595
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2596 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 148 200 48 302 334 398 270), lower := (rows 51 67 148 200 48 32 64 128 256), losses := [] }

theorem u2596 : Upper (D 1) (R 1) [50,65,144,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2596
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2597 : PairBound 9 := { available := 46, camps := [], pairs := [], upper := (rows 51 67 148 200 272 46 110 174 302), lower := (rows 51 67 148 200 272 32 64 128 256), losses := [] }

theorem u2597 : Upper (D 1) (R 1) [50,65,144,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2597
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2598 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 148 268 18 232 232 232 488), lower := (rows 51 67 148 268 18 32 64 128 256), losses := [] }

theorem u2598 : Upper (D 1) (R 1) [50,65,144,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2598
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2599 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 51 67 148 268 24 226 226 226 482), lower := (rows 51 67 148 268 24 32 64 128 256), losses := [] }

theorem u2599 : Upper (D 1) (R 1) [50,65,144,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2599
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2600 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 148 268 48 234 202 202 458), lower := (rows 51 67 148 268 48 32 64 128 256), losses := [] }

theorem u2600 : Upper (D 1) (R 1) [50,65,144,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2600
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2601 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 148 268 80 170 234 170 426), lower := (rows 51 67 148 268 80 32 64 128 256), losses := [] }

theorem u2601 : Upper (D 1) (R 1) [50,65,144,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2601
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2602 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 51 67 148 268 144 106 106 234 362), lower := (rows 51 67 148 268 144 32 64 128 256), losses := [] }

theorem u2602 : Upper (D 1) (R 1) [50,65,144,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2602
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2603 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 148 296 18 236 204 204 460), lower := (rows 51 67 148 296 18 32 64 128 256), losses := [] }

theorem u2603 : Upper (D 1) (R 1) [50,65,144,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2603
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2604 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 51 67 148 296 20 234 202 202 458), lower := (rows 51 67 148 296 20 32 64 128 256), losses := [] }

theorem u2604 : Upper (D 1) (R 1) [50,65,144,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2604
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2605 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 51 67 148 296 24 230 198 198 454), lower := (rows 51 67 148 296 24 32 64 128 256), losses := [] }

theorem u2605 : Upper (D 1) (R 1) [50,65,144,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2605
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2606 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 148 296 80 174 206 142 398), lower := (rows 51 67 148 296 80 32 64 128 256), losses := [] }

theorem u2606 : Upper (D 1) (R 1) [50,65,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2606
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2607 : PairBound 9 := { available := 78, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 51 67 148 296 144 110 78 206 334), lower := (rows 51 67 148 296 144 32 64 128 256), losses := [] }

theorem u2607 : Upper (D 1) (R 1) [50,65,144,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2607
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2608 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 148 328 18 172 236 172 428), lower := (rows 51 67 148 328 18 32 64 128 256), losses := [] }

theorem u2608 : Upper (D 1) (R 1) [50,65,144,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2608
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2609 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 67 148 328 20 170 234 170 426), lower := (rows 51 67 148 328 20 32 64 128 256), losses := [] }

theorem u2609 : Upper (D 1) (R 1) [50,65,144,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2609
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2610 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 51 67 148 328 24 166 230 166 422), lower := (rows 51 67 148 328 24 32 64 128 256), losses := [] }

theorem u2610 : Upper (D 1) (R 1) [50,65,144,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2610
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2611 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 148 328 48 174 206 142 398), lower := (rows 51 67 148 328 48 32 64 128 256), losses := [] }

theorem u2611 : Upper (D 1) (R 1) [50,65,144,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2611
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2612 : PairBound 9 := { available := 46, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 51 67 148 328 144 46 110 174 302), lower := (rows 51 67 148 328 144 32 64 128 256), losses := [] }

theorem u2612 : Upper (D 1) (R 1) [50,65,144,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2612
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2613 : PairBound 9 := { available := 108, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 148 392 18 108 108 236 364), lower := (rows 51 67 148 392 18 32 64 128 256), losses := [] }

theorem u2613 : Upper (D 1) (R 1) [50,65,144,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2613
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2614 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 51 67 148 392 20 106 106 234 362), lower := (rows 51 67 148 392 20 32 64 128 256), losses := [] }

theorem u2614 : Upper (D 1) (R 1) [50,65,144,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2614
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2615 : PairBound 9 := { available := 102, camps := [], pairs := [], upper := (rows 51 67 148 392 24 102 102 230 358), lower := (rows 51 67 148 392 24 32 64 128 256), losses := [] }

theorem u2615 : Upper (D 1) (R 1) [50,65,144,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2615
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2616 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 148 392 48 110 78 206 334), lower := (rows 51 67 148 392 48 32 64 128 256), losses := [] }

theorem u2616 : Upper (D 1) (R 1) [50,65,144,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2616
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2617 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 148 392 80 46 110 174 302), lower := (rows 51 67 148 392 80 32 64 128 256), losses := [] }

theorem u2617 : Upper (D 1) (R 1) [50,65,144,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2617
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2618 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 196 268 18 184 248 184 440), lower := (rows 51 67 196 268 18 32 64 128 256), losses := [] }

theorem u2618 : Upper (D 1) (R 1) [50,65,192,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2618
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2619 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 67 196 268 24 178 242 178 434), lower := (rows 51 67 196 268 24 32 64 128 256), losses := [] }

theorem u2619 : Upper (D 1) (R 1) [50,65,192,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2619
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2620 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 196 268 48 186 218 154 410), lower := (rows 51 67 196 268 48 32 64 128 256), losses := [] }

theorem u2620 : Upper (D 1) (R 1) [50,65,192,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2620
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2621_2 : Upper (D 1) (R 1) [50,65,192,260,128,2] 13 :=
  permutation_upper _ _ _ [50,65,192,260,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u594

theorem m2621_8 : Upper (D 1) (R 1) [50,65,192,260,128,8] 13 :=
  permutation_upper _ _ _ [50,65,192,260,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u595

theorem m2621_16 : Upper (D 1) (R 1) [50,65,192,260,128,16] 13 :=
  permutation_upper _ _ _ [50,65,192,260,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u596

def r2621 : Route 9 := (fun mask => (mask,id))

def c2621 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2621 : Upper (D 1) (R 1) [50,65,192,260,128] 13 := by
  apply FastRouting.sound _ _ [50,65,192,260,128] 13 (by decide) (choices 1) [2,8,16] r2621 c2621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2621_2
  · exact m2621_8
  · exact m2621_16

def b2622 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 196 280 18 172 236 172 428), lower := (rows 51 67 196 280 18 32 64 128 256), losses := [] }

theorem u2622 : Upper (D 1) (R 1) [50,65,192,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2622
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2623 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 67 196 280 20 170 234 170 426), lower := (rows 51 67 196 280 20 32 64 128 256), losses := [] }

theorem u2623 : Upper (D 1) (R 1) [50,65,192,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2623
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2624 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 51 67 196 280 24 166 230 166 422), lower := (rows 51 67 196 280 24 32 64 128 256), losses := [] }

theorem u2624 : Upper (D 1) (R 1) [50,65,192,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2624
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2625 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 196 280 48 174 206 142 398), lower := (rows 51 67 196 280 48 32 64 128 256), losses := [] }

theorem u2625 : Upper (D 1) (R 1) [50,65,192,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2625
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2626 : Route 9 := (fun mask => (mask,id))

def c2626 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2626 : Upper (D 1) (R 1) [50,65,192,272,128] 13 := by
  apply FastRouting.sound _ _ [50,65,192,272,128] 13 (by decide) (choices 1) [2,4,8] r2626 c2626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u597
  · exact u598
  · exact u599

def b2627 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 196 392 18 60 124 188 316), lower := (rows 51 67 196 392 18 32 64 128 256), losses := [] }

theorem u2627 : Upper (D 1) (R 1) [50,65,192,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2627
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2628 : PairBound 9 := { available := 58, camps := [], pairs := [], upper := (rows 51 67 196 392 20 58 122 186 314), lower := (rows 51 67 196 392 20 32 64 128 256), losses := [] }

theorem u2628 : Upper (D 1) (R 1) [50,65,192,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2628
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2629 : PairBound 9 := { available := 54, camps := [], pairs := [], upper := (rows 51 67 196 392 24 54 118 182 310), lower := (rows 51 67 196 392 24 32 64 128 256), losses := [] }

theorem u2629 : Upper (D 1) (R 1) [50,65,192,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2629
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2630 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 196 392 48 62 94 158 286), lower := (rows 51 67 196 392 48 32 64 128 256), losses := [] }

theorem u2630 : Upper (D 1) (R 1) [50,65,192,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2630
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2631 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 13 138 48 496 464 464 464), lower := (rows 51 70 13 138 48 32 64 128 256), losses := [] }

theorem u2631 : Upper (D 1) (R 1) [50,68,9,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2631
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2632 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 13 138 80 432 496 432 432), lower := (rows 51 70 13 138 80 32 64 128 256), losses := [] }

theorem u2632 : Upper (D 1) (R 1) [50,68,9,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2632
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2633 : PairBound 9 := { available := 368, camps := [], pairs := [(1,7)], upper := (rows 51 70 13 138 144 368 368 496 368), lower := (rows 51 70 13 138 144 32 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 49 81 0 273), good := (rows 371 70 367 10 368 32 64 0 256) }] }

theorem u2633 : Upper (D 1) (R 1) [50,68,9,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2633
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2634 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 70 13 138 272 240 240 240 496), lower := (rows 51 70 13 138 272 32 64 128 256), losses := [] }

theorem u2634 : Upper (D 1) (R 1) [50,68,9,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2634
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2635 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 13 266 48 240 208 208 464), lower := (rows 51 70 13 266 48 32 64 128 256), losses := [] }

theorem u2635 : Upper (D 1) (R 1) [50,68,9,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2635
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2636 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 13 266 80 176 240 176 432), lower := (rows 51 70 13 266 80 32 64 128 256), losses := [] }

theorem u2636 : Upper (D 1) (R 1) [50,68,9,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2636
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2637_16 : Upper (D 1) (R 1) [50,68,9,258,128,16] 13 :=
  permutation_upper _ _ _ [50,68,9,258,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u600

theorem m2637_64 : Upper (D 1) (R 1) [50,68,9,258,128,64] 13 :=
  permutation_upper _ _ _ [50,68,9,258,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u601

def r2637 : Route 9 := (fun mask => (mask,id))

def c2637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2637 : Upper (D 1) (R 1) [50,68,9,258,128] 13 := by
  apply FastRouting.sound _ _ [50,68,9,258,128] 13 (by decide) (choices 1) [16,64,128] r2637 c2637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2637_16
  · exact m2637_64
  · exact u602

def b2638 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 13 392 18 240 240 240 496), lower := (rows 51 70 13 392 18 32 64 128 256), losses := [] }

theorem u2638 : Upper (D 1) (R 1) [50,68,9,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2638
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2639 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 13 392 48 242 210 210 466), lower := (rows 51 70 13 392 48 32 64 128 256), losses := [] }

theorem u2639 : Upper (D 1) (R 1) [50,68,9,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2639
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2639
end Delivery.IrregularNine14.P01
