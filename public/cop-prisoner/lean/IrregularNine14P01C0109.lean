import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0045
import IrregularNine14P01C0046
import IrregularNine14P01C0047

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6540 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 21 44 474 490 458 458 458), lower := (rows 51 194 21 44 16 32 64 128 256), losses := [] }

theorem u6540 : Upper (D 1) (R 1) [50,192,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6540
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6541 : PairBound 9 := { available := 426, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 21 76 442 426 490 426 426), lower := (rows 51 194 21 76 16 32 64 128 256), losses := [] }

theorem u6541 : Upper (D 1) (R 1) [50,192,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6541
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6542 : PairBound 9 := { available := 398, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 21 104 414 430 462 398 398), lower := (rows 51 194 21 104 16 32 64 128 256), losses := [] }

theorem u6542 : Upper (D 1) (R 1) [50,192,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6542
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6543 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 21 266 252 236 236 236 492), lower := (rows 51 194 21 266 16 32 64 128 256), losses := [] }

theorem u6543 : Upper (D 1) (R 1) [50,192,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6543
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6544 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 21 268 250 234 234 234 490), lower := (rows 51 194 21 268 16 32 64 128 256), losses := [] }

theorem u6544 : Upper (D 1) (R 1) [50,192,17,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6544
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6545 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 21 296 222 238 206 206 462), lower := (rows 51 194 21 296 16 32 64 128 256), losses := [] }

theorem u6545 : Upper (D 1) (R 1) [50,192,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6545
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6546 : PairBound 9 := { available := 174, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 21 328 190 174 238 174 430), lower := (rows 51 194 21 328 16 32 64 128 256), losses := [] }

theorem u6546 : Upper (D 1) (R 1) [50,192,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6546
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6547 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 22 44 473 489 457 457 457), lower := (rows 51 194 22 44 16 32 64 128 256), losses := [] }

theorem u6547 : Upper (D 1) (R 1) [50,192,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6547
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6548 : PairBound 9 := { available := 428, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 22 73 444 428 492 428 428), lower := (rows 51 194 22 73 16 32 64 128 256), losses := [] }

theorem u6548 : Upper (D 1) (R 1) [50,192,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6548
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6549 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 22 76 441 425 489 425 425), lower := (rows 51 194 22 76 16 32 64 128 256), losses := [] }

theorem u6549 : Upper (D 1) (R 1) [50,192,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6549
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6550 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 22 104 413 429 461 397 397), lower := (rows 51 194 22 104 16 32 64 128 256), losses := [] }

theorem u6550 : Upper (D 1) (R 1) [50,192,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6550
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6551 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 22 265 252 236 236 236 492), lower := (rows 51 194 22 265 16 32 64 128 256), losses := [] }

theorem u6551 : Upper (D 1) (R 1) [50,192,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6551
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6552 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 22 268 249 233 233 233 489), lower := (rows 51 194 22 268 16 32 64 128 256), losses := [] }

theorem u6552 : Upper (D 1) (R 1) [50,192,18,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6552
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6553 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 22 296 221 237 205 205 461), lower := (rows 51 194 22 296 16 32 64 128 256), losses := [] }

theorem u6553 : Upper (D 1) (R 1) [50,192,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6553
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6554 : PairBound 9 := { available := 173, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 22 328 189 173 237 173 429), lower := (rows 51 194 22 328 16 32 64 128 256), losses := [] }

theorem u6554 : Upper (D 1) (R 1) [50,192,18,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6554
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6555 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 28 44 467 483 451 451 451), lower := (rows 51 194 28 44 16 32 64 128 256), losses := [] }

theorem u6555 : Upper (D 1) (R 1) [50,192,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6555
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6556 : PairBound 9 := { available := 422, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 28 73 438 422 486 422 422), lower := (rows 51 194 28 73 16 32 64 128 256), losses := [] }

theorem u6556 : Upper (D 1) (R 1) [50,192,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6556
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6557 : PairBound 9 := { available := 421, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 194 28 74 437 421 485 421 421), lower := (rows 51 194 28 74 16 32 64 128 256), losses := [] }

theorem u6557 : Upper (D 1) (R 1) [50,192,24,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6557
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6558 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 28 76 435 419 483 419 419), lower := (rows 51 194 28 76 16 32 64 128 256), losses := [] }

theorem u6558 : Upper (D 1) (R 1) [50,192,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6558
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6559 : Route 9 := (fun mask => (mask,id))

def c6559 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 64 => 6 | _ => 0)

theorem u6559 : Upper (D 1) (R 1) [50,192,24,96] 13 := by
  apply FastRouting.sound _ _ [50,192,24,96] 13 (by decide) (choices 1) [1,2,4,128,256] r6559 c6559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2758
  · exact u2759
  · exact u2760
  · exact u2761
  · exact u2762

def b6560 : PairBound 9 := { available := 295, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 194 28 200 311 295 359 423 295), lower := (rows 51 194 28 200 16 32 64 128 256), losses := [] }

theorem u6560 : Upper (D 1) (R 1) [50,192,24,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6560
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6561 : PairBound 9 := { available := 230, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 28 265 246 230 230 230 486), lower := (rows 51 194 28 265 16 32 64 128 256), losses := [] }

theorem u6561 : Upper (D 1) (R 1) [50,192,24,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6561
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6562 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6562 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6562 : Upper (D 1) (R 1) [50,192,24,258] 13 := by
  apply FastRouting.sound _ _ [50,192,24,258] 13 (by decide) (choices 1) [1,4,32,64] r6562 c6562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2763
  · exact u2764
  · exact u2765
  · exact u2766

def b6563 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 28 268 243 227 227 227 483), lower := (rows 51 194 28 268 16 32 64 128 256), losses := [] }

theorem u6563 : Upper (D 1) (R 1) [50,192,24,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6563
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6564 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6564 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6564 : Upper (D 1) (R 1) [50,192,24,288] 13 := by
  apply FastRouting.sound _ _ [50,192,24,288] 13 (by decide) (choices 1) [1,2,4,64] r6564 c6564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2767
  · exact u2768
  · exact u2769
  · exact u2770

def r6565 : Route 9 := (fun mask => (mask,id))

def c6565 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6565 : Upper (D 1) (R 1) [50,192,24,320] 13 := by
  apply FastRouting.sound _ _ [50,192,24,320] 13 (by decide) (choices 1) [1,2,4,32,128] r6565 c6565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2771
  · exact u2772
  · exact u2773
  · exact u2774
  · exact u2775

def b6566 : PairBound 9 := { available := 398, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 52 73 414 430 462 398 398), lower := (rows 51 194 52 73 16 32 64 128 256), losses := [] }

theorem u6566 : Upper (D 1) (R 1) [50,192,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6566
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6567 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 52 76 411 427 459 395 395), lower := (rows 51 194 52 76 16 32 64 128 256), losses := [] }

theorem u6567 : Upper (D 1) (R 1) [50,192,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6567
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6568 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 52 265 222 238 206 206 462), lower := (rows 51 194 52 265 16 32 64 128 256), losses := [] }

theorem u6568 : Upper (D 1) (R 1) [50,192,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6568
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6569 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 52 266 221 237 205 205 461), lower := (rows 51 194 52 266 16 32 64 128 256), losses := [] }

theorem u6569 : Upper (D 1) (R 1) [50,192,48,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6569
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6570 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 52 268 219 235 203 203 459), lower := (rows 51 194 52 268 16 32 64 128 256), losses := [] }

theorem u6570 : Upper (D 1) (R 1) [50,192,48,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6570
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6571 : PairBound 9 := { available := 143, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 52 328 159 175 207 143 399), lower := (rows 51 194 52 328 16 32 64 128 256), losses := [] }

theorem u6571 : Upper (D 1) (R 1) [50,192,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6571
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6572 : PairBound 9 := { available := 316, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 194 69 138 316 316 380 444 316), lower := (rows 51 194 69 138 16 32 64 128 256), losses := [] }

theorem u6572 : Upper (D 1) (R 1) [50,192,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6572
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6573 : Route 9 := (fun mask => (mask,id))

def c6573 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6573 : Upper (D 1) (R 1) [50,192,65,132] 13 := by
  apply FastRouting.sound _ _ [50,192,65,132] 13 (by decide) (choices 1) [2,8,32,256] r6573 c6573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2776
  · exact u2777
  · exact u2778
  · exact u2779

def r6574 : Route 9 := (fun mask => (mask,id))

def c6574 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | _ => 0)

theorem u6574 : Upper (D 1) (R 1) [50,192,65,144] 13 := by
  apply FastRouting.sound _ _ [50,192,65,144] 13 (by decide) (choices 1) [2,4,8,32,256] r6574 c6574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2780
  · exact u2781
  · exact u2782
  · exact u2783
  · exact u2784

def r6575 : Route 9 := (fun mask => (mask,id))

def c6575 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6575 : Upper (D 1) (R 1) [50,192,65,258] 13 := by
  apply FastRouting.sound _ _ [50,192,65,258] 13 (by decide) (choices 1) [4,8,32,128] r6575 c6575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2785
  · exact u2786
  · exact u2787
  · exact u2788

def r6576 : Route 9 := (fun mask => (mask,id))

def c6576 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6576 : Upper (D 1) (R 1) [50,192,65,260] 13 := by
  apply FastRouting.sound _ _ [50,192,65,260] 13 (by decide) (choices 1) [2,8,32,128] r6576 c6576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2789
  · exact u2790
  · exact u2791
  · exact u2792

def r6577 : Route 9 := (fun mask => (mask,id))

def c6577 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 256 => 8 | _ => 0)

theorem u6577 : Upper (D 1) (R 1) [50,192,65,272] 13 := by
  apply FastRouting.sound _ _ [50,192,65,272] 13 (by decide) (choices 1) [2,4,8,32,128] r6577 c6577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2793
  · exact u2794
  · exact u2795
  · exact u2796
  · exact u2797

def r6578 : Route 9 := (fun mask => (mask,id))

def c6578 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6578 : Upper (D 1) (R 1) [50,192,65,384] 13 := by
  apply FastRouting.sound _ _ [50,192,65,384] 13 (by decide) (choices 1) [2,4,8,32] r6578 c6578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2798
  · exact u2799
  · exact u2800
  · exact u2801

def b6579 : PairBound 9 := { available := 313, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 70 140 313 313 377 441 313), lower := (rows 51 194 70 140 16 32 64 128 256), losses := [] }

theorem u6579 : Upper (D 1) (R 1) [50,192,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6579
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6580 : PairBound 9 := { available := 301, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 70 152 317 301 365 429 301), lower := (rows 51 194 70 152 16 32 64 128 256), losses := [] }

theorem u6580 : Upper (D 1) (R 1) [50,192,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6580
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6581 : PairBound 9 := { available := 188, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 70 265 188 188 252 188 444), lower := (rows 51 194 70 265 16 32 64 128 256), losses := [] }

theorem u6581 : Upper (D 1) (R 1) [50,192,66,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6581
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6582 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 70 268 185 185 249 185 441), lower := (rows 51 194 70 268 16 32 64 128 256), losses := [] }

theorem u6582 : Upper (D 1) (R 1) [50,192,66,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6582
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6583 : PairBound 9 := { available := 173, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 70 280 189 173 237 173 429), lower := (rows 51 194 70 280 16 32 64 128 256), losses := [] }

theorem u6583 : Upper (D 1) (R 1) [50,192,66,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6583
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6584 : PairBound 9 := { available := 61, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 70 392 61 61 125 189 317), lower := (rows 51 194 70 392 16 32 64 128 256), losses := [] }

theorem u6584 : Upper (D 1) (R 1) [50,192,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6584
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6585 : PairBound 9 := { available := 307, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 76 140 307 307 371 435 307), lower := (rows 51 194 76 140 16 32 64 128 256), losses := [] }

theorem u6585 : Upper (D 1) (R 1) [50,192,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6585
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6586 : Route 9 := (fun mask => (mask,id))

def c6586 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6586 : Upper (D 1) (R 1) [50,192,72,144] 13 := by
  apply FastRouting.sound _ _ [50,192,72,144] 13 (by decide) (choices 1) [1,2,4,32,256] r6586 c6586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2802
  · exact u2803
  · exact u2804
  · exact u2805
  · exact u2806

def r6587 : Route 9 := (fun mask => (mask,id))

def c6587 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6587 : Upper (D 1) (R 1) [50,192,72,257] 13 := by
  apply FastRouting.sound _ _ [50,192,72,257] 13 (by decide) (choices 1) [2,4,32,128] r6587 c6587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2807
  · exact u2808
  · exact u2809
  · exact u2810

def r6588 : Route 9 := (fun mask => (mask,id))

def c6588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6588 : Upper (D 1) (R 1) [50,192,72,258] 13 := by
  apply FastRouting.sound _ _ [50,192,72,258] 13 (by decide) (choices 1) [1,4,32,128] r6588 c6588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2811
  · exact u2812
  · exact u2813
  · exact u2814

def b6589 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6)], upper := (rows 51 194 76 268 179 179 243 179 435), lower := (rows 51 194 76 268 16 32 64 128 256), losses := [] }

theorem u6589 : Upper (D 1) (R 1) [50,192,72,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6589
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6590 : Route 9 := (fun mask => (mask,id))

def c6590 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6590 : Upper (D 1) (R 1) [50,192,72,272] 13 := by
  apply FastRouting.sound _ _ [50,192,72,272] 13 (by decide) (choices 1) [1,2,4,32,128] r6590 c6590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2815
  · exact u2816
  · exact u2817
  · exact u2818
  · exact u2819

def r6591 : Route 9 := (fun mask => (mask,id))

def c6591 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6591 : Upper (D 1) (R 1) [50,192,72,384] 13 := by
  apply FastRouting.sound _ _ [50,192,72,384] 13 (by decide) (choices 1) [1,2,4,32] r6591 c6591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2820
  · exact u2821
  · exact u2822
  · exact u2823

def r6592 : Route 9 := (fun mask => (mask,id))

def c6592 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6592 : Upper (D 1) (R 1) [50,192,80,160] 13 := by
  apply FastRouting.sound _ _ [50,192,80,160] 13 (by decide) (choices 1) [1,2,4,8,256] r6592 c6592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2824
  · exact u2825
  · exact u2826
  · exact u2827
  · exact u2828

def r6593 : Route 9 := (fun mask => (mask,id))

def c6593 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 256 => 8 | _ => 0)

theorem u6593 : Upper (D 1) (R 1) [50,192,80,257] 13 := by
  apply FastRouting.sound _ _ [50,192,80,257] 13 (by decide) (choices 1) [2,4,8,32,128] r6593 c6593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2829
  · exact u2830
  · exact u2831
  · exact u2832
  · exact u2833

def r6594 : Route 9 := (fun mask => (mask,id))

def c6594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6594 : Upper (D 1) (R 1) [50,192,80,258] 13 := by
  apply FastRouting.sound _ _ [50,192,80,258] 13 (by decide) (choices 1) [1,4,8,32,128] r6594 c6594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2834
  · exact u2835
  · exact u2836
  · exact u2837
  · exact u2838

def r6595 : Route 9 := (fun mask => (mask,id))

def c6595 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6595 : Upper (D 1) (R 1) [50,192,80,260] 13 := by
  apply FastRouting.sound _ _ [50,192,80,260] 13 (by decide) (choices 1) [1,2,8,32,128] r6595 c6595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2839
  · exact u2840
  · exact u2841
  · exact u2842
  · exact u2843

def r6596 : Route 9 := (fun mask => (mask,id))

def c6596 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6596 : Upper (D 1) (R 1) [50,192,80,288] 13 := by
  apply FastRouting.sound _ _ [50,192,80,288] 13 (by decide) (choices 1) [1,2,4,8,128] r6596 c6596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2844
  · exact u2845
  · exact u2846
  · exact u2847
  · exact u2848

def r6597 : Route 9 := (fun mask => (mask,id))

def c6597 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6597 : Upper (D 1) (R 1) [50,192,80,384] 13 := by
  apply FastRouting.sound _ _ [50,192,80,384] 13 (by decide) (choices 1) [1,2,4,8,32] r6597 c6597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2849
  · exact u2850
  · exact u2851
  · exact u2852
  · exact u2853

def b6598 : PairBound 9 := { available := 62, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 196 265 62 62 126 190 318), lower := (rows 51 194 196 265 16 32 64 128 256), losses := [] }

theorem u6598 : Upper (D 1) (R 1) [50,192,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6598
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6599 : PairBound 9 := { available := 61, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 196 266 61 61 125 189 317), lower := (rows 51 194 196 266 16 32 64 128 256), losses := [] }

theorem u6599 : Upper (D 1) (R 1) [50,192,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6599
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u6599
end Delivery.IrregularNine14.P01
