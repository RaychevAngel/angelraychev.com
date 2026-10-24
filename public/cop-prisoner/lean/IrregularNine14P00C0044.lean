import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0023
import IrregularNine14P00C0024
import IrregularNine14P00C0025

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2640 : Route 9 := (fun mask => (mask,id))

def c2640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2640 : Upper (D 0) (R 0) [50,192,24,320] 13 := by
  apply FastRouting.sound _ _ [50,192,24,320] 13 (by decide) (choices 1) [1,4,32,128] r2640 c2640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1433
  · exact u1434
  · exact u1435
  · exact u1436

def b2641 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 52 76 409 425 457 393 393), lower := (rows 51 194 52 76 16 32 64 128 256), losses := [] }

theorem u2641 : Upper (D 0) (R 0) [50,192,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2641
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2642 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 52 265 221 237 205 205 461), lower := (rows 51 194 52 265 16 32 64 128 256), losses := [] }

theorem u2642 : Upper (D 0) (R 0) [50,192,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2642
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2643 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 52 268 217 233 201 201 457), lower := (rows 51 194 52 268 16 32 64 128 256), losses := [] }

theorem u2643 : Upper (D 0) (R 0) [50,192,48,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2643
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2644 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 52 328 157 173 205 141 397), lower := (rows 51 194 52 328 16 32 64 128 256), losses := [] }

theorem u2644 : Upper (D 0) (R 0) [50,192,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2644
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2645 : PairBound 9 := { available := 313, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 69 140 313 313 377 441 313), lower := (rows 51 194 69 140 16 32 64 128 256), losses := [] }

theorem u2645 : Upper (D 0) (R 0) [50,192,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2645
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2646 : PairBound 9 := { available := 301, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 69 152 317 301 365 429 301), lower := (rows 51 194 69 152 16 32 64 128 256), losses := [] }

theorem u2646 : Upper (D 0) (R 0) [50,192,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2646
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2647 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 69 265 188 188 252 188 444), lower := (rows 51 194 69 265 16 32 64 128 256), losses := [] }

theorem u2647 : Upper (D 0) (R 0) [50,192,65,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2647
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2648 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 69 268 185 185 249 185 441), lower := (rows 51 194 69 268 16 32 64 128 256), losses := [] }

theorem u2648 : Upper (D 0) (R 0) [50,192,65,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2648
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2649 : PairBound 9 := { available := 173, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 69 280 189 173 237 173 429), lower := (rows 51 194 69 280 16 32 64 128 256), losses := [] }

theorem u2649 : Upper (D 0) (R 0) [50,192,65,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2649
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2650 : PairBound 9 := { available := 61, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 69 392 61 61 125 189 317), lower := (rows 51 194 69 392 16 32 64 128 256), losses := [] }

theorem u2650 : Upper (D 0) (R 0) [50,192,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2650
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2651 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 51 194 76 140 305 305 369 433 305), lower := (rows 51 194 76 140 16 32 64 128 256), losses := [] }

theorem u2651 : Upper (D 0) (R 0) [50,192,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2651
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2652 : Route 9 := (fun mask => (mask,id))

def c2652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2652 : Upper (D 0) (R 0) [50,192,72,144] 13 := by
  apply FastRouting.sound _ _ [50,192,72,144] 13 (by decide) (choices 1) [1,4,32,256] r2652 c2652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1437
  · exact u1438
  · exact u1439
  · exact u1440

def r2653 : Route 9 := (fun mask => (mask,id))

def c2653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2653 : Upper (D 0) (R 0) [50,192,72,257] 13 := by
  apply FastRouting.sound _ _ [50,192,72,257] 13 (by decide) (choices 1) [1,4,32,128] r2653 c2653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1441
  · exact u1442
  · exact u1443
  · exact u1444

def b2654 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6)], upper := (rows 51 194 76 268 177 177 241 177 433), lower := (rows 51 194 76 268 16 32 64 128 256), losses := [] }

theorem u2654 : Upper (D 0) (R 0) [50,192,72,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2654
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2655 : Route 9 := (fun mask => (mask,id))

def c2655 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2655 : Upper (D 0) (R 0) [50,192,72,272] 13 := by
  apply FastRouting.sound _ _ [50,192,72,272] 13 (by decide) (choices 1) [1,4,32,128] r2655 c2655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1445
  · exact u1446
  · exact u1447
  · exact u1448

def r2656 : Route 9 := (fun mask => (mask,id))

def c2656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2656 : Upper (D 0) (R 0) [50,192,72,384] 13 := by
  apply FastRouting.sound _ _ [50,192,72,384] 13 (by decide) (choices 1) [1,4,32] r2656 c2656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1449
  · exact u1450
  · exact u1451

def r2657 : Route 9 := (fun mask => (mask,id))

def c2657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2657 : Upper (D 0) (R 0) [50,192,80,160] 13 := by
  apply FastRouting.sound _ _ [50,192,80,160] 13 (by decide) (choices 1) [1,4,8,256] r2657 c2657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1452
  · exact u1453
  · exact u1454
  · exact u1455

def r2658 : Route 9 := (fun mask => (mask,id))

def c2658 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2658 : Upper (D 0) (R 0) [50,192,80,257] 13 := by
  apply FastRouting.sound _ _ [50,192,80,257] 13 (by decide) (choices 1) [1,4,8,32,128] r2658 c2658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1456
  · exact u1457
  · exact u1458
  · exact u1459
  · exact u1460

def r2659 : Route 9 := (fun mask => (mask,id))

def c2659 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2659 : Upper (D 0) (R 0) [50,192,80,260] 13 := by
  apply FastRouting.sound _ _ [50,192,80,260] 13 (by decide) (choices 1) [1,8,32,128] r2659 c2659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1461
  · exact u1462
  · exact u1463
  · exact u1464

def r2660 : Route 9 := (fun mask => (mask,id))

def c2660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2660 : Upper (D 0) (R 0) [50,192,80,288] 13 := by
  apply FastRouting.sound _ _ [50,192,80,288] 13 (by decide) (choices 1) [1,4,8,128] r2660 c2660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1465
  · exact u1466
  · exact u1467
  · exact u1468

def r2661 : Route 9 := (fun mask => (mask,id))

def c2661 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2661 : Upper (D 0) (R 0) [50,192,80,384] 13 := by
  apply FastRouting.sound _ _ [50,192,80,384] 13 (by decide) (choices 1) [1,4,8,32] r2661 c2661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1469
  · exact u1470
  · exact u1471
  · exact u1472

def b2662 : PairBound 9 := { available := 61, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 194 196 265 61 61 125 189 317), lower := (rows 51 194 196 265 16 32 64 128 256), losses := [] }

theorem u2662 : Upper (D 0) (R 0) [50,192,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2662
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2663 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 194 196 268 57 57 121 185 313), lower := (rows 51 194 196 268 16 32 64 128 256), losses := [] }

theorem u2663 : Upper (D 0) (R 0) [50,192,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2663
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2664 : PairBound 9 := { available := 45, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 194 196 280 61 45 109 173 301), lower := (rows 51 194 196 280 16 32 64 128 256), losses := [] }

theorem u2664 : Upper (D 0) (R 0) [50,192,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2664
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2665 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 259 13 28 240 224 224 224 480), lower := (rows 51 259 13 28 16 32 64 128 256), losses := [] }

theorem u2665 : Upper (D 0) (R 0) [50,257,9,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2665
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2666 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 51 259 13 76 240 240 240 240 496), lower := (rows 51 259 13 76 16 32 64 128 256), losses := [] }

theorem u2666 : Upper (D 0) (R 0) [50,257,9,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2666
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2667 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 51 259 13 88 244 228 228 228 484), lower := (rows 51 259 13 88 16 32 64 128 256), losses := [] }

theorem u2667 : Upper (D 0) (R 0) [50,257,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2667
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2668 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 51 259 13 200 244 244 244 244 500), lower := (rows 51 259 13 200 16 32 64 128 256), losses := [] }

theorem u2668 : Upper (D 0) (R 0) [50,257,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2668
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2669 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 259 21 44 216 232 200 200 456), lower := (rows 51 259 21 44 16 32 64 128 256), losses := [] }

theorem u2669 : Upper (D 0) (R 0) [50,257,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2669
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2670 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 259 21 76 248 232 232 232 488), lower := (rows 51 259 21 76 16 32 64 128 256), losses := [] }

theorem u2670 : Upper (D 0) (R 0) [50,257,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2670
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2671 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 259 21 104 220 236 204 204 460), lower := (rows 51 259 21 104 16 32 64 128 256), losses := [] }

theorem u2671 : Upper (D 0) (R 0) [50,257,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2671
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2672 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 259 21 200 252 236 236 236 492), lower := (rows 51 259 21 200 16 32 64 128 256), losses := [] }

theorem u2672 : Upper (D 0) (R 0) [50,257,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2672
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2673 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 51 259 28 44 209 225 193 193 449), lower := (rows 51 259 28 44 16 32 64 128 256), losses := [] }

theorem u2673 : Upper (D 0) (R 0) [50,257,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2673
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2674 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 28 73 244 228 228 228 484), lower := (rows 51 259 28 73 16 32 64 128 256), losses := [] }

theorem u2674 : Upper (D 0) (R 0) [50,257,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2674
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2675 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 259 28 76 241 225 225 225 481), lower := (rows 51 259 28 76 16 32 64 128 256), losses := [] }

theorem u2675 : Upper (D 0) (R 0) [50,257,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2675
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2676 : Route 9 := (fun mask => (mask,id))

def c2676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2676 : Upper (D 0) (R 0) [50,257,24,96] 13 := by
  apply FastRouting.sound _ _ [50,257,24,96] 13 (by decide) (choices 1) [1,4,64,128] r2676 c2676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1473
  · exact u1474
  · exact u1475
  · exact u1476

def r2677 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2677 : Upper (D 0) (R 0) [50,257,24,192] 13 := by
  apply FastRouting.sound _ _ [50,257,24,192] 13 (by decide) (choices 1) [1,4,32,64] r2677 c2677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1477
  · exact u1478
  · exact u1479
  · exact u1480

def b2678 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 259 52 76 217 233 201 201 457), lower := (rows 51 259 52 76 16 32 64 128 256), losses := [] }

theorem u2678 : Upper (D 0) (R 0) [50,257,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2678
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2679 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 259 52 200 221 237 205 205 461), lower := (rows 51 259 52 200 16 32 64 128 256), losses := [] }

theorem u2679 : Upper (D 0) (R 0) [50,257,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2679
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2680 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 259 69 76 184 184 248 184 440), lower := (rows 51 259 69 76 16 32 64 128 256), losses := [] }

theorem u2680 : Upper (D 0) (R 0) [50,257,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2680
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2681 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 51 259 69 88 188 172 236 172 428), lower := (rows 51 259 69 88 16 32 64 128 256), losses := [] }

theorem u2681 : Upper (D 0) (R 0) [50,257,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2681
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2682 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 51 259 69 140 248 248 248 248 504), lower := (rows 51 259 69 140 16 32 64 128 256), losses := [] }

theorem u2682 : Upper (D 0) (R 0) [50,257,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2682
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2683 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 51 259 69 152 252 236 236 236 492), lower := (rows 51 259 69 152 16 32 64 128 256), losses := [] }

theorem u2683 : Upper (D 0) (R 0) [50,257,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2683
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2684 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 51 259 69 200 188 188 252 188 444), lower := (rows 51 259 69 200 16 32 64 128 256), losses := [] }

theorem u2684 : Upper (D 0) (R 0) [50,257,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2684
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2685 : PairBound 9 := { available := 177, camps := [{ cop := 6, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 76 76 177 177 241 177 433), lower := (rows 51 259 76 76 16 32 64 128 256), losses := [] }

theorem u2685 : Upper (D 0) (R 0) [50,257,72,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2685
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2686 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 76 88 181 165 229 165 421), lower := (rows 51 259 76 88 16 32 64 128 256), losses := [] }

theorem u2686 : Upper (D 0) (R 0) [50,257,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2686
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m2687_128 : Upper (D 0) (R 0) [50,257,72,132,128] 13 :=
  permutation_upper _ _ _ [50,257,72,132,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1483

def r2687 : Route 9 := (fun mask => (mask,id))

def c2687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2687 : Upper (D 0) (R 0) [50,257,72,132] 13 := by
  apply FastRouting.sound _ _ [50,257,72,132] 13 (by decide) (choices 1) [1,32,64,128] r2687 c2687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1481
  · exact u1482
  · exact u1483
  · exact m2687_128

def r2688 : Route 9 := (fun mask => (mask,id))

def c2688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2688 : Upper (D 0) (R 0) [50,257,72,144] 13 := by
  apply FastRouting.sound _ _ [50,257,72,144] 13 (by decide) (choices 1) [1,4,32,64,128] r2688 c2688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1484
  · exact u1485
  · exact u1486
  · exact u1487
  · exact u1488

def b2689 : PairBound 9 := { available := 181, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 76 200 181 181 245 181 437), lower := (rows 51 259 76 200 16 32 64 128 256), losses := [] }

theorem u2689 : Upper (D 0) (R 0) [50,257,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2689
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2690 : Route 9 := (fun mask => (mask,id))

def c2690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2690 : Upper (D 0) (R 0) [50,257,80,96] 13 := by
  apply FastRouting.sound _ _ [50,257,80,96] 13 (by decide) (choices 1) [1,4,8,128] r2690 c2690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1489
  · exact u1490
  · exact u1491
  · exact u1492

def r2691 : Route 9 := (fun mask => (mask,id))

def c2691 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2691 : Upper (D 0) (R 0) [50,257,80,160] 13 := by
  apply FastRouting.sound _ _ [50,257,80,160] 13 (by decide) (choices 1) [1,4,8,64,128] r2691 c2691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1493
  · exact u1494
  · exact u1495
  · exact u1496
  · exact u1497

def r2692 : Route 9 := (fun mask => (mask,id))

def c2692 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2692 : Upper (D 0) (R 0) [50,257,80,192] 13 := by
  apply FastRouting.sound _ _ [50,257,80,192] 13 (by decide) (choices 1) [1,4,8,32,128] r2692 c2692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1498
  · exact u1499
  · exact u1500
  · exact u1501
  · exact u1502

def b2693 : PairBound 9 := { available := 61, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 51 259 196 200 61 61 125 189 317), lower := (rows 51 259 196 200 16 32 64 128 256), losses := [] }

theorem u2693 : Upper (D 0) (R 0) [50,257,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2693
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2694 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 262 13 25 240 224 224 224 480), lower := (rows 51 262 13 25 16 32 64 128 256), losses := [] }

theorem u2694 : Upper (D 0) (R 0) [50,260,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2694
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2695 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 51 262 13 56 209 225 193 193 449), lower := (rows 51 262 13 56 16 32 64 128 256), losses := [] }

theorem u2695 : Upper (D 0) (R 0) [50,260,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2695
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2696 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 262 13 73 240 240 240 240 496), lower := (rows 51 262 13 73 16 32 64 128 256), losses := [] }

theorem u2696 : Upper (D 0) (R 0) [50,260,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2696
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2697 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 262 13 88 241 225 225 225 481), lower := (rows 51 262 13 88 16 32 64 128 256), losses := [] }

theorem u2697 : Upper (D 0) (R 0) [50,260,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2697
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2698 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2698 : Upper (D 0) (R 0) [50,260,9,192] 13 := by
  apply FastRouting.sound _ _ [50,260,9,192] 13 (by decide) (choices 1) [1,32,64] r2698 c2698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1503
  · exact u1504
  · exact u1505

def b2699 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 262 69 25 248 232 232 232 488), lower := (rows 51 262 69 25 16 32 64 128 256), losses := [] }

theorem u2699 : Upper (D 0) (R 0) [50,260,65,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2699
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u2699
end Delivery.IrregularNine14.P00
