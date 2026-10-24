import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0525
import IrregularNine14P06C0526
import IrregularNine14P06C0527
import IrregularNine14P06C0528
import IrregularNine14P06C0529

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r41520 : Route 9 := (fun mask => (mask,id))

def c41520 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41520 : Upper (D 6) (R 6) [10,36,144,257] 13 := by
  apply FastRouting.sound _ _ [10,36,144,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41520 c41520
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31533
  · exact u31534
  · exact u31535
  · exact u31536
  · exact u31537
  · exact u31538
  · exact u31539
  · exact u31540
  · exact u31541
  · exact u31542

def b41521 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 148 266 117 101 101 229 357), lower := (rows 11 38 148 266 16 32 64 128 256), losses := [] }

theorem u41521 : Upper (D 6) (R 6) [10,36,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41522 : Route 9 := (fun mask => (mask,id))

def c41522 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41522 : Upper (D 6) (R 6) [10,36,144,260] 13 := by
  apply FastRouting.sound _ _ [10,36,144,260] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41522 c41522
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31543
  · exact u31544
  · exact u31545
  · exact u31546
  · exact u31547
  · exact u31548

def r41523 : Route 9 := (fun mask => (mask,id))

def c41523 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41523 : Upper (D 6) (R 6) [10,36,144,288] 13 := by
  apply FastRouting.sound _ _ [10,36,144,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41523 c41523
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31549
  · exact u31550
  · exact u31551
  · exact u31552
  · exact u31553
  · exact u31554

def r41524 : Route 9 := (fun mask => (mask,id))

def c41524 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41524 : Upper (D 6) (R 6) [10,36,144,320] 13 := by
  apply FastRouting.sound _ _ [10,36,144,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41524 c41524
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31555
  · exact u31556
  · exact u31557
  · exact u31558
  · exact u31559
  · exact u31560
  · exact u31561
  · exact u31562
  · exact u31563
  · exact u31564

def b41525 : PairBound 9 := { available := 373, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 196 11 373 373 373 501 373), lower := (rows 11 38 196 11 16 32 64 128 256), losses := [] }

theorem u41525 : Upper (D 6) (R 6) [10,36,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41526 : PairBound 9 := { available := 371, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 196 13 371 371 371 499 371), lower := (rows 11 38 196 13 16 32 64 128 256), losses := [] }

theorem u41526 : Upper (D 6) (R 6) [10,36,192,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41527 : PairBound 9 := { available := 369, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 196 14 369 369 369 497 369), lower := (rows 11 38 196 14 16 32 64 128 256), losses := [] }

theorem u41527 : Upper (D 6) (R 6) [10,36,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41528 : Route 9 := (fun mask => (mask,id))

def c41528 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41528 : Upper (D 6) (R 6) [10,36,192,17] 13 := by
  apply FastRouting.sound _ _ [10,36,192,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41528 c41528
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31565
  · exact u31566
  · exact u31567
  · exact u31568
  · exact u31569
  · exact u31570
  · exact u31571
  · exact u31572
  · exact u31573
  · exact u31574
  · exact u31575
  · exact u31576
  · exact u31577
  · exact u31578
  · exact u31579

def b41529 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 196 26 373 357 357 485 357), lower := (rows 11 38 196 26 16 32 64 128 256), losses := [] }

theorem u41529 : Upper (D 6) (R 6) [10,36,192,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41530 : Route 9 := (fun mask => (mask,id))

def c41530 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41530 : Upper (D 6) (R 6) [10,36,192,20] 13 := by
  apply FastRouting.sound _ _ [10,36,192,20] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r41530 c41530
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31580
  · exact u31581
  · exact u31582
  · exact u31583
  · exact u31584
  · exact u31585
  · exact u31586
  · exact u31587
  · exact u31588
  · exact u31589

def b41531 : PairBound 9 := { available := 343, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 196 41 343 375 343 471 343), lower := (rows 11 38 196 41 16 32 64 128 256), losses := [] }

theorem u41531 : Upper (D 6) (R 6) [10,36,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41532 : PairBound 9 := { available := 341, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 196 42 341 373 341 469 341), lower := (rows 11 38 196 42 16 32 64 128 256), losses := [] }

theorem u41532 : Upper (D 6) (R 6) [10,36,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41533 : PairBound 9 := { available := 339, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 9, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 38 196 44 339 371 339 467 339), lower := (rows 11 38 196 44 16 32 64 128 256), losses := [] }

theorem u41533 : Upper (D 6) (R 6) [10,36,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41534 : Route 9 := (fun mask => (mask,id))

def c41534 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41534 : Upper (D 6) (R 6) [10,36,192,48] 13 := by
  apply FastRouting.sound _ _ [10,36,192,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41534 c41534
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31590
  · exact u31591
  · exact u31592
  · exact u31593
  · exact u31594
  · exact u31595
  · exact u31596
  · exact u31597
  · exact u31598
  · exact u31599

def r41535 : Route 9 := (fun mask => (mask,id))

def c41535 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41535 : Upper (D 6) (R 6) [10,36,192,65] 13 := by
  apply FastRouting.sound _ _ [10,36,192,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r41535 c41535
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31600
  · exact u31601
  · exact u31602
  · exact u31603
  · exact u31604
  · exact u31605
  · exact u31606
  · exact u31607
  · exact u31608
  · exact u31609

def b41536 : PairBound 9 := { available := 309, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 196 74 309 309 373 437 309), lower := (rows 11 38 196 74 16 32 64 128 256), losses := [] }

theorem u41536 : Upper (D 6) (R 6) [10,36,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41537 : PairBound 9 := { available := 307, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 38 196 76 307 307 371 435 307), lower := (rows 11 38 196 76 16 32 64 128 256), losses := [] }

theorem u41537 : Upper (D 6) (R 6) [10,36,192,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41538 : Route 9 := (fun mask => (mask,id))

def c41538 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41538 : Upper (D 6) (R 6) [10,36,192,80] 13 := by
  apply FastRouting.sound _ _ [10,36,192,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r41538 c41538
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31610
  · exact u31611
  · exact u31612
  · exact u31613
  · exact u31614
  · exact u31615
  · exact u31616
  · exact u31617
  · exact u31618
  · exact u31619

def r41539 : Route 9 := (fun mask => (mask,id))

def c41539 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41539 : Upper (D 6) (R 6) [10,36,192,96] 13 := by
  apply FastRouting.sound _ _ [10,36,192,96] 13 (by decide) (choices 2) [3,5,6,257,258,260] r41539 c41539
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31620
  · exact u31621
  · exact u31622
  · exact u31623
  · exact u31624
  · exact u31625

def r41540 : Route 9 := (fun mask => (mask,id))

def c41540 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41540 : Upper (D 6) (R 6) [10,36,192,257] 13 := by
  apply FastRouting.sound _ _ [10,36,192,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41540 c41540
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31626
  · exact u31627
  · exact u31628
  · exact u31629
  · exact u31630
  · exact u31631
  · exact u31632
  · exact u31633
  · exact u31634
  · exact u31635

def b41541 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 196 266 117 117 117 245 373), lower := (rows 11 38 196 266 16 32 64 128 256), losses := [] }

theorem u41541 : Upper (D 6) (R 6) [10,36,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41542 : Route 9 := (fun mask => (mask,id))

def c41542 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41542 : Upper (D 6) (R 6) [10,36,192,260] 13 := by
  apply FastRouting.sound _ _ [10,36,192,260] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41542 c41542
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31636
  · exact u31637
  · exact u31638
  · exact u31639
  · exact u31640
  · exact u31641

def r41543 : Route 9 := (fun mask => (mask,id))

def c41543 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41543 : Upper (D 6) (R 6) [10,36,192,272] 13 := by
  apply FastRouting.sound _ _ [10,36,192,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41543 c41543
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31642
  · exact u31643
  · exact u31644
  · exact u31645
  · exact u31646
  · exact u31647
  · exact u31648
  · exact u31649
  · exact u31650
  · exact u31651

def r41544 : Route 9 := (fun mask => (mask,id))

def c41544 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41544 : Upper (D 6) (R 6) [10,36,192,288] 13 := by
  apply FastRouting.sound _ _ [10,36,192,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41544 c41544
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31652
  · exact u31653
  · exact u31654
  · exact u31655
  · exact u31656
  · exact u31657

def r41545 : Route 9 := (fun mask => (mask,id))

def c41545 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41545 : Upper (D 6) (R 6) [10,36,192,320] 13 := by
  apply FastRouting.sound _ _ [10,36,192,320] 13 (by decide) (choices 2) [3,5,6,33,34,36] r41545 c41545
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31658
  · exact u31659
  · exact u31660
  · exact u31661
  · exact u31662
  · exact u31663

def b41546 : PairBound 9 := { available := 117, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 388 11 117 117 117 245 373), lower := (rows 11 38 388 11 16 32 64 128 256), losses := [] }

theorem u41546 : Upper (D 6) (R 6) [10,36,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41547 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 388 13 115 115 115 243 371), lower := (rows 11 38 388 13 16 32 64 128 256), losses := [] }

theorem u41547 : Upper (D 6) (R 6) [10,36,384,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41548 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 388 14 113 113 113 241 369), lower := (rows 11 38 388 14 16 32 64 128 256), losses := [] }

theorem u41548 : Upper (D 6) (R 6) [10,36,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41549 : Route 9 := (fun mask => (mask,id))

def c41549 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41549 : Upper (D 6) (R 6) [10,36,384,17] 13 := by
  apply FastRouting.sound _ _ [10,36,384,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41549 c41549
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31664
  · exact u31665
  · exact u31666
  · exact u31667
  · exact u31668
  · exact u31669
  · exact u31670
  · exact u31671
  · exact u31672
  · exact u31673

def b41550 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 388 26 117 101 101 229 357), lower := (rows 11 38 388 26 16 32 64 128 256), losses := [] }

theorem u41550 : Upper (D 6) (R 6) [10,36,384,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41551 : Route 9 := (fun mask => (mask,id))

def c41551 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41551 : Upper (D 6) (R 6) [10,36,384,20] 13 := by
  apply FastRouting.sound _ _ [10,36,384,20] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41551 c41551
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31674
  · exact u31675
  · exact u31676
  · exact u31677
  · exact u31678
  · exact u31679

def b41552 : PairBound 9 := { available := 87, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 388 41 87 119 87 215 343), lower := (rows 11 38 388 41 16 32 64 128 256), losses := [] }

theorem u41552 : Upper (D 6) (R 6) [10,36,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41553 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 388 42 85 117 85 213 341), lower := (rows 11 38 388 42 16 32 64 128 256), losses := [] }

theorem u41553 : Upper (D 6) (R 6) [10,36,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41554 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 9, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 38 388 44 83 115 83 211 339), lower := (rows 11 38 388 44 16 32 64 128 256), losses := [] }

theorem u41554 : Upper (D 6) (R 6) [10,36,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41555 : Route 9 := (fun mask => (mask,id))

def c41555 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41555 : Upper (D 6) (R 6) [10,36,384,48] 13 := by
  apply FastRouting.sound _ _ [10,36,384,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41555 c41555
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31680
  · exact u31681
  · exact u31682
  · exact u31683
  · exact u31684
  · exact u31685

def r41556 : Route 9 := (fun mask => (mask,id))

def c41556 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41556 : Upper (D 6) (R 6) [10,36,384,65] 13 := by
  apply FastRouting.sound _ _ [10,36,384,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41556 c41556
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31686
  · exact u31687
  · exact u31688
  · exact u31689
  · exact u31690
  · exact u31691
  · exact u31692
  · exact u31693
  · exact u31694
  · exact u31695

def b41557 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 388 74 117 117 117 245 373), lower := (rows 11 38 388 74 16 32 64 128 256), losses := [] }

theorem u41557 : Upper (D 6) (R 6) [10,36,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41558 : Route 9 := (fun mask => (mask,id))

def c41558 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41558 : Upper (D 6) (R 6) [10,36,384,68] 13 := by
  apply FastRouting.sound _ _ [10,36,384,68] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41558 c41558
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31696
  · exact u31697
  · exact u31698
  · exact u31699
  · exact u31700
  · exact u31701

def r41559 : Route 9 := (fun mask => (mask,id))

def c41559 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41559 : Upper (D 6) (R 6) [10,36,384,80] 13 := by
  apply FastRouting.sound _ _ [10,36,384,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41559 c41559
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31702
  · exact u31703
  · exact u31704
  · exact u31705
  · exact u31706
  · exact u31707
  · exact u31708
  · exact u31709
  · exact u31710
  · exact u31711

def r41560 : Route 9 := (fun mask => (mask,id))

def c41560 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41560 : Upper (D 6) (R 6) [10,36,384,96] 13 := by
  apply FastRouting.sound _ _ [10,36,384,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41560 c41560
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31712
  · exact u31713
  · exact u31714
  · exact u31715
  · exact u31716
  · exact u31717

def b41561 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 37 11 468 484 452 452 452), lower := (rows 11 50 37 11 16 32 64 128 256), losses := [] }

theorem u41561 : Upper (D 6) (R 6) [10,48,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41562 : PairBound 9 := { available := 454, camps := [{ cop := 1, region := 13, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 37 13 470 486 454 454 454), lower := (rows 11 50 37 13 16 32 64 128 256), losses := [] }

theorem u41562 : Upper (D 6) (R 6) [10,48,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41563 : PairBound 9 := { available := 453, camps := [{ cop := 1, region := 13, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 37 14 469 485 453 453 453), lower := (rows 11 50 37 14 16 32 64 128 256), losses := [] }

theorem u41563 : Upper (D 6) (R 6) [10,48,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41564 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41564 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41564 : Upper (D 6) (R 6) [10,48,33,65] 13 := by
  apply FastRouting.sound _ _ [10,48,33,65] 13 (by decide) (choices 2) [6,66,68,130,132,192,384] r41564 c41564
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31718
  · exact u31719
  · exact u31720
  · exact u31721
  · exact u31722
  · exact u31723
  · exact u31724

def b41565 : PairBound 9 := { available := 453, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 37 74 469 485 453 453 453), lower := (rows 11 50 37 74 16 32 64 128 256), losses := [] }

theorem u41565 : Upper (D 6) (R 6) [10,48,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41566 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41566 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41566 : Upper (D 6) (R 6) [10,48,33,68] 13 := by
  apply FastRouting.sound _ _ [10,48,33,68] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r41566 c41566
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31725
  · exact u31726
  · exact u31727
  · exact u31728
  · exact u31729
  · exact u31730
  · exact u31731
  · exact u31732
  · exact u31733
  · exact u31734
  · exact u31735

def r41567 : Route 9 := (fun mask => (mask,id))

def c41567 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41567 : Upper (D 6) (R 6) [10,48,33,129] 13 := by
  apply FastRouting.sound _ _ [10,48,33,129] 13 (by decide) (choices 2) [6,66,68,258,260,320] r41567 c41567
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31736
  · exact u31737
  · exact u31738
  · exact u31739
  · exact u31740
  · exact u31741

def b41568 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 37 138 341 357 325 453 325), lower := (rows 11 50 37 138 16 32 64 128 256), losses := [] }

theorem u41568 : Upper (D 6) (R 6) [10,48,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41569 : Route 9 := (fun mask => (mask,id))

def c41569 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41569 : Upper (D 6) (R 6) [10,48,33,132] 13 := by
  apply FastRouting.sound _ _ [10,48,33,132] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41569 c41569
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31742
  · exact u31743
  · exact u31744
  · exact u31745
  · exact u31746
  · exact u31747
  · exact u31748
  · exact u31749
  · exact u31750
  · exact u31751

def r41570 : Route 9 := (fun mask => (mask,id))

def c41570 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41570 : Upper (D 6) (R 6) [10,48,33,192] 13 := by
  apply FastRouting.sound _ _ [10,48,33,192] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41570 c41570
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31752
  · exact u31753
  · exact u31754
  · exact u31755
  · exact u31756
  · exact u31757
  · exact u31758
  · exact u31759
  · exact u31760
  · exact u31761

def r41571 : Route 9 := (fun mask => (mask,id))

def c41571 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41571 : Upper (D 6) (R 6) [10,48,33,384] 13 := by
  apply FastRouting.sound _ _ [10,48,33,384] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41571 c41571
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31762
  · exact u31763
  · exact u31764
  · exact u31765
  · exact u31766
  · exact u31767

def b41572 : PairBound 9 := { available := 484, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 69 11 500 484 484 484 484), lower := (rows 11 50 69 11 16 32 64 128 256), losses := [] }

theorem u41572 : Upper (D 6) (R 6) [10,48,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41573 : PairBound 9 := { available := 486, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 11 50 69 13 502 486 486 486 486), lower := (rows 11 50 69 13 16 32 64 128 256), losses := [] }

theorem u41573 : Upper (D 6) (R 6) [10,48,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41574 : PairBound 9 := { available := 485, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 69 14 501 485 485 485 485), lower := (rows 11 50 69 14 16 32 64 128 256), losses := [] }

theorem u41574 : Upper (D 6) (R 6) [10,48,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41575 : PairBound 9 := { available := 454, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 69 41 470 486 454 454 454), lower := (rows 11 50 69 41 16 32 64 128 256), losses := [] }

theorem u41575 : Upper (D 6) (R 6) [10,48,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41576 : PairBound 9 := { available := 453, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 69 42 469 485 453 453 453), lower := (rows 11 50 69 42 16 32 64 128 256), losses := [] }

theorem u41576 : Upper (D 6) (R 6) [10,48,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41577 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41577 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41577 : Upper (D 6) (R 6) [10,48,65,36] 13 := by
  apply FastRouting.sound _ _ [10,48,65,36] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r41577 c41577
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31768
  · exact u31769
  · exact u31770
  · exact u31771
  · exact u31772
  · exact u31773
  · exact u31774
  · exact u31775
  · exact u31776
  · exact u31777
  · exact u31778

def b41578 : PairBound 9 := { available := 422, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 2, region := 8, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 50 69 73 438 422 486 422 422), lower := (rows 11 50 69 73 16 32 64 128 256), losses := [] }

theorem u41578 : Upper (D 6) (R 6) [10,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41579 : PairBound 9 := { available := 421, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6),(2,1),(4,1)], upper := (rows 11 50 69 74 437 421 485 421 421), lower := (rows 11 50 69 74 16 32 64 128 256), losses := [] }

theorem u41579 : Upper (D 6) (R 6) [10,48,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u41579
end Delivery.IrregularNine14.P06
