import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0044
import IrregularNine14P01C0045

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6480 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 140 328 179 179 243 179 435), lower := (rows 51 70 140 328 16 32 64 128 256), losses := [] }

theorem u6480 : Upper (D 1) (R 1) [50,68,136,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6480
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6481 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 140 392 115 115 115 243 371), lower := (rows 51 70 140 392 16 32 64 128 256), losses := [] }

theorem u6481 : Upper (D 1) (R 1) [50,68,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6481
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6482 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 261 26 248 232 232 232 488), lower := (rows 51 70 261 26 16 32 64 128 256), losses := [] }

theorem u6482 : Upper (D 1) (R 1) [50,68,257,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6482
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6483 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 70 261 56 218 234 202 202 458), lower := (rows 51 70 261 56 16 32 64 128 256), losses := [] }

theorem u6483 : Upper (D 1) (R 1) [50,68,257,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6483
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6484 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 261 74 184 184 248 184 440), lower := (rows 51 70 261 74 16 32 64 128 256), losses := [] }

theorem u6484 : Upper (D 1) (R 1) [50,68,257,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6484
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6485 : Route 9 := (fun mask => (mask,id))

def c6485 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6485 : Upper (D 1) (R 1) [50,68,257,80] 13 := by
  apply FastRouting.sound _ _ [50,68,257,80] 13 (by decide) (choices 1) [2,8,32,128] r6485 c6485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2686
  · exact u2687
  · exact u2688
  · exact u2689

def r6486 : Route 9 := (fun mask => (mask,id))

def c6486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u6486 : Upper (D 1) (R 1) [50,68,257,130] 13 := by
  apply FastRouting.sound _ _ [50,68,257,130] 13 (by decide) (choices 1) [8,32,64,128] r6486 c6486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2690
  · exact u2691
  · exact u2692
  · exact u2693

def r6487 : Route 9 := (fun mask => (mask,id))

def c6487 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u6487 : Upper (D 1) (R 1) [50,68,257,144] 13 := by
  apply FastRouting.sound _ _ [50,68,257,144] 13 (by decide) (choices 1) [2,8,32,64,128] r6487 c6487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2694
  · exact u2695
  · exact u2696
  · exact u2697
  · exact u2698

def r6488 : Route 9 := (fun mask => (mask,id))

def c6488 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6488 : Upper (D 1) (R 1) [50,68,257,192] 13 := by
  apply FastRouting.sound _ _ [50,68,257,192] 13 (by decide) (choices 1) [2,8,32,128] r6488 c6488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2699
  · exact u2700
  · exact u2701
  · exact u2702

def b6489 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 268 11 240 240 240 240 496), lower := (rows 51 70 268 11 16 32 64 128 256), losses := [] }

theorem u6489 : Upper (D 1) (R 1) [50,68,264,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6489
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6490 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 70 268 25 242 226 226 226 482), lower := (rows 51 70 268 25 16 32 64 128 256), losses := [] }

theorem u6490 : Upper (D 1) (R 1) [50,68,264,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6490
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6491 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 268 26 241 225 225 225 481), lower := (rows 51 70 268 26 16 32 64 128 256), losses := [] }

theorem u6491 : Upper (D 1) (R 1) [50,68,264,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6491
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6492 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 70 268 56 211 227 195 195 451), lower := (rows 51 70 268 56 16 32 64 128 256), losses := [] }

theorem u6492 : Upper (D 1) (R 1) [50,68,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6492
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6493 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 268 73 178 178 242 178 434), lower := (rows 51 70 268 73 16 32 64 128 256), losses := [] }

theorem u6493 : Upper (D 1) (R 1) [50,68,264,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6493
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6494 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 268 74 177 177 241 177 433), lower := (rows 51 70 268 74 16 32 64 128 256), losses := [] }

theorem u6494 : Upper (D 1) (R 1) [50,68,264,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6494
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6495 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 268 88 179 163 227 163 419), lower := (rows 51 70 268 88 16 32 64 128 256), losses := [] }

theorem u6495 : Upper (D 1) (R 1) [50,68,264,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6495
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6496 : Route 9 := (fun mask => (mask,id))

def c6496 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6496 : Upper (D 1) (R 1) [50,68,264,129] 13 := by
  apply FastRouting.sound _ _ [50,68,264,129] 13 (by decide) (choices 1) [2,32,64,128] r6496 c6496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2703
  · exact u2704
  · exact u2705
  · exact u2706

def r6497 : Route 9 := (fun mask => (mask,id))

def c6497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6497 : Upper (D 1) (R 1) [50,68,264,130] 13 := by
  apply FastRouting.sound _ _ [50,68,264,130] 13 (by decide) (choices 1) [1,32,64,128] r6497 c6497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2707
  · exact u2708
  · exact u2709
  · exact u2710

def r6498 : Route 9 := (fun mask => (mask,id))

def c6498 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6498 : Upper (D 1) (R 1) [50,68,264,144] 13 := by
  apply FastRouting.sound _ _ [50,68,264,144] 13 (by decide) (choices 1) [1,2,32,64,128] r6498 c6498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2711
  · exact u2712
  · exact u2713
  · exact u2714
  · exact u2715

def b6499 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 268 200 179 179 243 179 435), lower := (rows 51 70 268 200 16 32 64 128 256), losses := [] }

theorem u6499 : Upper (D 1) (R 1) [50,68,264,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6499
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6500 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 388 11 248 248 248 248 504), lower := (rows 51 70 388 11 16 32 64 128 256), losses := [] }

theorem u6500 : Upper (D 1) (R 1) [50,68,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6500
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6501 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 70 388 25 250 234 234 234 490), lower := (rows 51 70 388 25 16 32 64 128 256), losses := [] }

theorem u6501 : Upper (D 1) (R 1) [50,68,384,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6501
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6502 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 70 388 26 249 233 233 233 489), lower := (rows 51 70 388 26 16 32 64 128 256), losses := [] }

theorem u6502 : Upper (D 1) (R 1) [50,68,384,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6502
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6503 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 70 388 56 219 235 203 203 459), lower := (rows 51 70 388 56 16 32 64 128 256), losses := [] }

theorem u6503 : Upper (D 1) (R 1) [50,68,384,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6503
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6504 : Route 9 := (fun mask => (mask,id))

def c6504 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6504 : Upper (D 1) (R 1) [50,68,384,65] 13 := by
  apply FastRouting.sound _ _ [50,68,384,65] 13 (by decide) (choices 1) [2,8,32,128] r6504 c6504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2716
  · exact u2717
  · exact u2718
  · exact u2719

def b6505 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 388 74 185 185 249 185 441), lower := (rows 51 70 388 74 16 32 64 128 256), losses := [] }

theorem u6505 : Upper (D 1) (R 1) [50,68,384,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6505
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6506 : Route 9 := (fun mask => (mask,id))

def c6506 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6506 : Upper (D 1) (R 1) [50,68,384,80] 13 := by
  apply FastRouting.sound _ _ [50,68,384,80] 13 (by decide) (choices 1) [1,2,8,32,128] r6506 c6506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2720
  · exact u2721
  · exact u2722
  · exact u2723
  · exact u2724

def r6507 : Route 9 := (fun mask => (mask,id))

def c6507 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6507 : Upper (D 1) (R 1) [50,68,384,129] 13 := by
  apply FastRouting.sound _ _ [50,68,384,129] 13 (by decide) (choices 1) [2,8,32,64] r6507 c6507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2725
  · exact u2726
  · exact u2727
  · exact u2728

def b6508 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 51 70 388 138 121 121 121 249 377), lower := (rows 51 70 388 138 16 32 64 128 256), losses := [] }

theorem u6508 : Upper (D 1) (R 1) [50,68,384,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6508
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6509 : Route 9 := (fun mask => (mask,id))

def c6509 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6509 : Upper (D 1) (R 1) [50,68,384,144] 13 := by
  apply FastRouting.sound _ _ [50,68,384,144] 13 (by decide) (choices 1) [1,2,8,32,64] r6509 c6509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2729
  · exact u2730
  · exact u2731
  · exact u2732
  · exact u2733

def r6510 : Route 9 := (fun mask => (mask,id))

def c6510 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6510 : Upper (D 1) (R 1) [50,68,384,192] 13 := by
  apply FastRouting.sound _ _ [50,68,384,192] 13 (by decide) (choices 1) [1,2,8,32] r6510 c6510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2734
  · exact u2735
  · exact u2736
  · exact u2737

def b6511 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 7 28 504 488 488 488 488), lower := (rows 51 194 7 28 16 32 64 128 256), losses := [] }

theorem u6511 : Upper (D 1) (R 1) [50,192,3,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6511
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6512 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 7 76 440 440 504 440 440), lower := (rows 51 194 7 76 16 32 64 128 256), losses := [] }

theorem u6512 : Upper (D 1) (R 1) [50,192,3,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6512
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6513 : PairBound 9 := { available := 428, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 7 88 444 428 492 428 428), lower := (rows 51 194 7 88 16 32 64 128 256), losses := [] }

theorem u6513 : Upper (D 1) (R 1) [50,192,3,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6513
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6514 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 7 268 248 248 248 248 504), lower := (rows 51 194 7 268 16 32 64 128 256), losses := [] }

theorem u6514 : Upper (D 1) (R 1) [50,192,3,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6514
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6515 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 7 280 252 236 236 236 492), lower := (rows 51 194 7 280 16 32 64 128 256), losses := [] }

theorem u6515 : Upper (D 1) (R 1) [50,192,3,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6515
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6516 : PairBound 9 := { available := 188, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 7 328 188 188 252 188 444), lower := (rows 51 194 7 328 16 32 64 128 256), losses := [] }

theorem u6516 : Upper (D 1) (R 1) [50,192,3,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6516
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6517 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 13 14 496 496 496 496 496), lower := (rows 51 194 13 14 16 32 64 128 256), losses := [] }

theorem u6517 : Upper (D 1) (R 1) [50,192,9,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6517
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6518 : PairBound 9 := { available := 484, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 13 26 500 484 484 484 484), lower := (rows 51 194 13 26 16 32 64 128 256), losses := [] }

theorem u6518 : Upper (D 1) (R 1) [50,192,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6518
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6519 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 13 28 498 482 482 482 482), lower := (rows 51 194 13 28 16 32 64 128 256), losses := [] }

theorem u6519 : Upper (D 1) (R 1) [50,192,9,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6519
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6520 : PairBound 9 := { available := 454, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 13 56 470 486 454 454 454), lower := (rows 51 194 13 56 16 32 64 128 256), losses := [] }

theorem u6520 : Upper (D 1) (R 1) [50,192,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6520
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6521 : PairBound 9 := { available := 436, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 194 13 74 436 436 500 436 436), lower := (rows 51 194 13 74 16 32 64 128 256), losses := [] }

theorem u6521 : Upper (D 1) (R 1) [50,192,9,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6521
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6522 : PairBound 9 := { available := 434, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 51 194 13 76 434 434 498 434 434), lower := (rows 51 194 13 76 16 32 64 128 256), losses := [] }

theorem u6522 : Upper (D 1) (R 1) [50,192,9,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6522
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6523 : PairBound 9 := { available := 422, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 13 88 438 422 486 422 422), lower := (rows 51 194 13 88 16 32 64 128 256), losses := [] }

theorem u6523 : Upper (D 1) (R 1) [50,192,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6523
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6524 : PairBound 9 := { available := 310, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 194 13 200 310 310 374 438 310), lower := (rows 51 194 13 200 16 32 64 128 256), losses := [] }

theorem u6524 : Upper (D 1) (R 1) [50,192,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6524
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6525 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6525 : Upper (D 1) (R 1) [50,192,9,258] 13 := by
  apply FastRouting.sound _ _ [50,192,9,258] 13 (by decide) (choices 1) [4,32,64] r6525 c6525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2738
  · exact u2739
  · exact u2740

def r6526 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6526 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6526 : Upper (D 1) (R 1) [50,192,9,260] 13 := by
  apply FastRouting.sound _ _ [50,192,9,260] 13 (by decide) (choices 1) [2,32,64] r6526 c6526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2741
  · exact u2742
  · exact u2743

def b6527 : PairBound 9 := { available := 230, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 13 280 246 230 230 230 486), lower := (rows 51 194 13 280 16 32 64 128 256), losses := [] }

theorem u6527 : Upper (D 1) (R 1) [50,192,9,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6527
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6528 : Route 9 := (fun mask => (mask,id))

def c6528 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6528 : Upper (D 1) (R 1) [50,192,9,320] 13 := by
  apply FastRouting.sound _ _ [50,192,9,320] 13 (by decide) (choices 1) [2,4,32,128] r6528 c6528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2744
  · exact u2745
  · exact u2746
  · exact u2747

def b6529 : PairBound 9 := { available := 484, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 14 25 500 484 484 484 484), lower := (rows 51 194 14 25 16 32 64 128 256), losses := [] }

theorem u6529 : Upper (D 1) (R 1) [50,192,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6529
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6530 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 14 28 497 481 481 481 481), lower := (rows 51 194 14 28 16 32 64 128 256), losses := [] }

theorem u6530 : Upper (D 1) (R 1) [50,192,10,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6530
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6531 : PairBound 9 := { available := 453, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 14 56 469 485 453 453 453), lower := (rows 51 194 14 56 16 32 64 128 256), losses := [] }

theorem u6531 : Upper (D 1) (R 1) [50,192,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6531
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6532 : PairBound 9 := { available := 436, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 194 14 73 436 436 500 436 436), lower := (rows 51 194 14 73 16 32 64 128 256), losses := [] }

theorem u6532 : Upper (D 1) (R 1) [50,192,10,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6532
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6533 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 14 76 433 433 497 433 433), lower := (rows 51 194 14 76 16 32 64 128 256), losses := [] }

theorem u6533 : Upper (D 1) (R 1) [50,192,10,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6533
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6534 : PairBound 9 := { available := 421, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 194 14 88 437 421 485 421 421), lower := (rows 51 194 14 88 16 32 64 128 256), losses := [] }

theorem u6534 : Upper (D 1) (R 1) [50,192,10,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6534
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6535 : PairBound 9 := { available := 309, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 14 200 309 309 373 437 309), lower := (rows 51 194 14 200 16 32 64 128 256), losses := [] }

theorem u6535 : Upper (D 1) (R 1) [50,192,10,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6535
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6536 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6536 : Upper (D 1) (R 1) [50,192,10,257] 13 := by
  apply FastRouting.sound _ _ [50,192,10,257] 13 (by decide) (choices 1) [4,32,64] r6536 c6536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2748
  · exact u2749
  · exact u2750

def r6537 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6537 : Upper (D 1) (R 1) [50,192,10,260] 13 := by
  apply FastRouting.sound _ _ [50,192,10,260] 13 (by decide) (choices 1) [1,32,64] r6537 c6537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2751
  · exact u2752
  · exact u2753

def r6538 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6538 : Upper (D 1) (R 1) [50,192,10,272] 13 := by
  apply FastRouting.sound _ _ [50,192,10,272] 13 (by decide) (choices 1) [1,4,32,64] r6538 c6538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2754
  · exact u2755
  · exact u2756
  · exact u2757

def b6539 : PairBound 9 := { available := 181, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 194 14 328 181 181 245 181 437), lower := (rows 51 194 14 328 16 32 64 128 256), losses := [] }

theorem u6539 : Upper (D 1) (R 1) [50,192,10,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6539
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u6539
end Delivery.IrregularNine14.P01
