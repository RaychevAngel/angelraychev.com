import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0408
import IrregularNine14P06C0409
import IrregularNine14P06C0410

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38580 : Route 9 := (fun mask => (mask,id))

def c38580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38580 : Upper (D 6) (R 6) [34,136,320,66,36] 13 := by
  apply FastRouting.sound _ _ [34,136,320,66,36] 13 (by decide) (choices 1) [1,4,16] r38580 c38580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24511
  · exact u24512
  · exact u24513

def b38581 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 324 88 19 37 101 165 293), lower := (rows 35 138 324 88 19 32 64 128 256), losses := [] }

theorem u38581 : Upper (D 6) (R 6) [34,136,320,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38582 : Route 9 := (fun mask => (mask,id))

def c38582 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38582 : Upper (D 6) (R 6) [34,136,320,80,5] 13 := by
  apply FastRouting.sound _ _ [34,136,320,80,5] 13 (by decide) (choices 1) [1,2,4] r38582 c38582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24514
  · exact u24515
  · exact u24516

def b38583 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 324, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 35 138 324 88 22 37 101 165 293), lower := (rows 35 138 324 88 22 32 64 128 256), losses := [{ target := 6, region := (rows 25 10 4 8 16 48 0 144 272), good := (rows 35 139 260 443 439 32 0 128 256) }] }

theorem u38583 : Upper (D 6) (R 6) [34,136,320,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38584 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 324 88 49 39 71 135 263), lower := (rows 35 138 324 88 49 32 64 128 256), losses := [] }

theorem u38584 : Upper (D 6) (R 6) [34,136,320,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38585 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 324 88 50 37 69 133 261), lower := (rows 35 138 324 88 50 32 64 128 256), losses := [] }

theorem u38585 : Upper (D 6) (R 6) [34,136,320,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38586 : Route 9 := (fun mask => (mask,id))

def c38586 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38586 : Upper (D 6) (R 6) [34,136,320,80,36] 13 := by
  apply FastRouting.sound _ _ [34,136,320,80,36] 13 (by decide) (choices 1) [1,2,4] r38586 c38586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24517
  · exact u24518
  · exact u24519

def b38587 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 138 324 104 19 53 85 149 277), lower := (rows 35 138 324 104 19 32 64 128 256), losses := [] }

theorem u38587 : Upper (D 6) (R 6) [34,136,320,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38588 : Route 9 := (fun mask => (mask,id))

def c38588 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38588 : Upper (D 6) (R 6) [34,136,320,96,5] 13 := by
  apply FastRouting.sound _ _ [34,136,320,96,5] 13 (by decide) (choices 1) [1,2,4,16] r38588 c38588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24520
  · exact u24521
  · exact u24522
  · exact u24523

def b38589 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 138 324 104 22 53 85 149 277), lower := (rows 35 138 324 104 22 32 64 128 256), losses := [] }

theorem u38589 : Upper (D 6) (R 6) [34,136,320,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38590 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 194 44 25 19 356 324 452 324), lower := (rows 35 194 44 25 19 32 64 128 256), losses := [] }

theorem u38590 : Upper (D 6) (R 6) [34,192,40,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38591 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 28, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 194 44 25 21 358 326 454 326), lower := (rows 35 194 44 25 21 32 64 128 256), losses := [] }

theorem u38591 : Upper (D 6) (R 6) [34,192,40,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38592 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 44 25 22 357 325 453 325), lower := (rows 35 194 44 25 22 32 64 128 256), losses := [] }

theorem u38592 : Upper (D 6) (R 6) [34,192,40,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38593 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 44 25 81 294 326 390 262), lower := (rows 35 194 44 25 81 32 64 128 256), losses := [] }

theorem u38593 : Upper (D 6) (R 6) [34,192,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38594 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 44 25 82 293 325 389 261), lower := (rows 35 194 44 25 82 32 64 128 256), losses := [] }

theorem u38594 : Upper (D 6) (R 6) [34,192,40,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38595 : Route 9 := (fun mask => (mask,id))

def c38595 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38595 : Upper (D 6) (R 6) [34,192,40,17,68] 13 := by
  apply FastRouting.sound _ _ [34,192,40,17,68] 13 (by decide) (choices 1) [1,2,4,256] r38595 c38595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24524
  · exact u24525
  · exact u24526
  · exact u24527

def b38596 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 44 25 273 102 70 198 326), lower := (rows 35 194 44 25 273 32 64 128 256), losses := [] }

theorem u38596 : Upper (D 6) (R 6) [34,192,40,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38597 : Route 9 := (fun mask => (mask,id))

def c38597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38597 : Upper (D 6) (R 6) [34,192,40,17,258] 13 := by
  apply FastRouting.sound _ _ [34,192,40,17,258] 13 (by decide) (choices 1) [1,4,64] r38597 c38597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24528
  · exact u24529
  · exact u24530

def r38598 : Route 9 := (fun mask => (mask,id))

def c38598 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38598 : Upper (D 6) (R 6) [34,192,40,17,260] 13 := by
  apply FastRouting.sound _ _ [34,192,40,17,260] 13 (by decide) (choices 1) [1,2,4,64] r38598 c38598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24531
  · exact u24532
  · exact u24533
  · exact u24534

def r38599 : Route 9 := (fun mask => (mask,id))

def c38599 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38599 : Upper (D 6) (R 6) [34,192,40,17,320] 13 := by
  apply FastRouting.sound _ _ [34,192,40,17,320] 13 (by decide) (choices 1) [1,2,4] r38599 c38599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24535
  · exact u24536
  · exact u24537

def b38600 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 44 26 21 357 325 453 325), lower := (rows 35 194 44 26 21 32 64 128 256), losses := [] }

theorem u38600 : Upper (D 6) (R 6) [34,192,40,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38601 : Route 9 := (fun mask => (mask,id))

def c38601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38601 : Upper (D 6) (R 6) [34,192,40,18,65] 13 := by
  apply FastRouting.sound _ _ [34,192,40,18,65] 13 (by decide) (choices 1) [1,4,256] r38601 c38601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24538
  · exact u24539
  · exact u24540

def r38602 : Route 9 := (fun mask => (mask,id))

def c38602 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38602 : Upper (D 6) (R 6) [34,192,40,18,68] 13 := by
  apply FastRouting.sound _ _ [34,192,40,18,68] 13 (by decide) (choices 1) [1,4,256] r38602 c38602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24541
  · exact u24542
  · exact u24543

def r38603 : Route 9 := (fun mask => (mask,id))

def c38603 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38603 : Upper (D 6) (R 6) [34,192,40,18,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,18,257] 13 (by decide) (choices 1) [1,4,64] r38603 c38603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24544
  · exact u24545
  · exact u24546

def r38604 : Route 9 := (fun mask => (mask,id))

def c38604 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38604 : Upper (D 6) (R 6) [34,192,40,18,260] 13 := by
  apply FastRouting.sound _ _ [34,192,40,18,260] 13 (by decide) (choices 1) [1,4,64] r38604 c38604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24547
  · exact u24548
  · exact u24549

def r38605 : Route 9 := (fun mask => (mask,id))

def c38605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38605 : Upper (D 6) (R 6) [34,192,40,18,320] 13 := by
  apply FastRouting.sound _ _ [34,192,40,18,320] 13 (by decide) (choices 1) [1,4] r38605 c38605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24550
  · exact u24551

def b38606 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 44 28 19 357 325 453 325), lower := (rows 35 194 44 28 19 32 64 128 256), losses := [] }

theorem u38606 : Upper (D 6) (R 6) [34,192,40,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38607 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 28, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 194 44 28 21 355 323 451 323), lower := (rows 35 194 44 28 21 32 64 128 256), losses := [] }

theorem u38607 : Upper (D 6) (R 6) [34,192,40,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38608 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 44 28 22 353 321 449 321), lower := (rows 35 194 44 28 22 32 64 128 256), losses := [] }

theorem u38608 : Upper (D 6) (R 6) [34,192,40,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38609 : Route 9 := (fun mask => (mask,id))

def c38609 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38609 : Upper (D 6) (R 6) [34,192,40,20,65] 13 := by
  apply FastRouting.sound _ _ [34,192,40,20,65] 13 (by decide) (choices 1) [1,2,4,256] r38609 c38609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24552
  · exact u24553
  · exact u24554
  · exact u24555

def b38610 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 44 28 82 293 325 389 261), lower := (rows 35 194 44 28 82 32 64 128 256), losses := [] }

theorem u38610 : Upper (D 6) (R 6) [34,192,40,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38611 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 44 28 84 291 323 387 259), lower := (rows 35 194 44 28 84 32 64 128 256), losses := [] }

theorem u38611 : Upper (D 6) (R 6) [34,192,40,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38612 : Route 9 := (fun mask => (mask,id))

def c38612 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38612 : Upper (D 6) (R 6) [34,192,40,20,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,20,257] 13 (by decide) (choices 1) [1,2,4,64] r38612 c38612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24556
  · exact u24557
  · exact u24558
  · exact u24559

def r38613 : Route 9 := (fun mask => (mask,id))

def c38613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38613 : Upper (D 6) (R 6) [34,192,40,20,258] 13 := by
  apply FastRouting.sound _ _ [34,192,40,20,258] 13 (by decide) (choices 1) [1,4,64] r38613 c38613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24560
  · exact u24561
  · exact u24562

def b38614 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 44 28 276 99 67 195 323), lower := (rows 35 194 44 28 276 32 64 128 256), losses := [] }

theorem u38614 : Upper (D 6) (R 6) [34,192,40,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38615 : Route 9 := (fun mask => (mask,id))

def c38615 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38615 : Upper (D 6) (R 6) [34,192,40,20,320] 13 := by
  apply FastRouting.sound _ _ [34,192,40,20,320] 13 (by decide) (choices 1) [1,2,4] r38615 c38615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24563
  · exact u24564
  · exact u24565

def b38616 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 44 73 19 308 340 404 276), lower := (rows 35 194 44 73 19 32 64 128 256), losses := [] }

theorem u38616 : Upper (D 6) (R 6) [34,192,40,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38617 : PairBound 9 := { available := 278, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 4, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(3,5)], upper := (rows 35 194 44 73 21 310 342 406 278), lower := (rows 35 194 44 73 21 32 64 128 256), losses := [] }

theorem u38617 : Upper (D 6) (R 6) [34,192,40,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38618 : Route 9 := (fun mask => (mask,id))

def c38618 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38618 : Upper (D 6) (R 6) [34,192,40,65,6] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,6] 13 (by decide) (choices 1) [1,4,16,256] r38618 c38618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24566
  · exact u24567
  · exact u24568
  · exact u24569

def r38619 : Route 9 := (fun mask => (mask,id))

def c38619 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38619 : Upper (D 6) (R 6) [34,192,40,65,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,257] 13 (by decide) (choices 1) [2,4,16] r38619 c38619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24570
  · exact u24571
  · exact u24572

def r38620 : Route 9 := (fun mask => (mask,id))

def c38620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38620 : Upper (D 6) (R 6) [34,192,40,65,258] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,258] 13 (by decide) (choices 1) [1,4,16] r38620 c38620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24573
  · exact u24574
  · exact u24575

def r38621 : Route 9 := (fun mask => (mask,id))

def c38621 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38621 : Upper (D 6) (R 6) [34,192,40,65,260] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,260] 13 (by decide) (choices 1) [1,2,4,16] r38621 c38621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24576
  · exact u24577
  · exact u24578
  · exact u24579

def b38622 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 44 76 19 309 341 405 277), lower := (rows 35 194 44 76 19 32 64 128 256), losses := [] }

theorem u38622 : Upper (D 6) (R 6) [34,192,40,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38623 : PairBound 9 := { available := 275, camps := [{ cop := 4, region := 483, targets := 4 },{ cop := 4, region := 450, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 194 44 76 21 307 339 403 275), lower := (rows 35 194 44 76 21 32 64 128 256), losses := [] }

theorem u38623 : Upper (D 6) (R 6) [34,192,40,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38624 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 483, targets := 4 },{ cop := 4, region := 289, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 44 76 22 305 337 401 273), lower := (rows 35 194 44 76 22 32 64 128 256), losses := [] }

theorem u38624 : Upper (D 6) (R 6) [34,192,40,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38625 : Route 9 := (fun mask => (mask,id))

def c38625 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38625 : Upper (D 6) (R 6) [34,192,40,68,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,68,257] 13 (by decide) (choices 1) [1,2,4,16] r38625 c38625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24580
  · exact u24581
  · exact u24582
  · exact u24583

def r38626 : Route 9 := (fun mask => (mask,id))

def c38626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38626 : Upper (D 6) (R 6) [34,192,40,68,258] 13 := by
  apply FastRouting.sound _ _ [34,192,40,68,258] 13 (by decide) (choices 1) [1,4,16] r38626 c38626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24584
  · exact u24585
  · exact u24586

def r38627 : Route 9 := (fun mask => (mask,id))

def c38627 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38627 : Upper (D 6) (R 6) [34,192,40,68,260] 13 := by
  apply FastRouting.sound _ _ [34,192,40,68,260] 13 (by decide) (choices 1) [1,2,16] r38627 c38627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24587
  · exact u24588
  · exact u24589

def b38628 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 44 88 19 293 325 389 261), lower := (rows 35 194 44 88 19 32 64 128 256), losses := [] }

theorem u38628 : Upper (D 6) (R 6) [34,192,40,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38629 : Route 9 := (fun mask => (mask,id))

def c38629 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38629 : Upper (D 6) (R 6) [34,192,40,80,5] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,5] 13 (by decide) (choices 1) [1,2,4,256] r38629 c38629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24590
  · exact u24591
  · exact u24592
  · exact u24593

def r38630 : Route 9 := (fun mask => (mask,id))

def c38630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38630 : Upper (D 6) (R 6) [34,192,40,80,6] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,6] 13 (by decide) (choices 1) [1,4,256] r38630 c38630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24594
  · exact u24595
  · exact u24596

def r38631 : Route 9 := (fun mask => (mask,id))

def c38631 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38631 : Upper (D 6) (R 6) [34,192,40,80,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,257] 13 (by decide) (choices 1) [1,2,4] r38631 c38631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24597
  · exact u24598
  · exact u24599

def r38632 : Route 9 := (fun mask => (mask,id))

def c38632 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38632 : Upper (D 6) (R 6) [34,192,40,80,258] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,258] 13 (by decide) (choices 1) [1,4] r38632 c38632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24600
  · exact u24601

def r38633 : Route 9 := (fun mask => (mask,id))

def c38633 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38633 : Upper (D 6) (R 6) [34,192,40,80,260] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,260] 13 (by decide) (choices 1) [1,2,4] r38633 c38633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24602
  · exact u24603
  · exact u24604

def b38634 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 44 265 19 116 84 212 340), lower := (rows 35 194 44 265 19 32 64 128 256), losses := [] }

theorem u38634 : Upper (D 6) (R 6) [34,192,40,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38635 : PairBound 9 := { available := 86, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(1,5),(3,5)], upper := (rows 35 194 44 265 21 118 86 214 342), lower := (rows 35 194 44 265 21 32 64 128 256), losses := [] }

theorem u38635 : Upper (D 6) (R 6) [34,192,40,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38636 : Route 9 := (fun mask => (mask,id))

def c38636 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38636 : Upper (D 6) (R 6) [34,192,40,257,6] 13 := by
  apply FastRouting.sound _ _ [34,192,40,257,6] 13 (by decide) (choices 1) [1,4,16,64] r38636 c38636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24605
  · exact u24606
  · exact u24607
  · exact u24608

def r38637 : Route 9 := (fun mask => (mask,id))

def c38637 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38637 : Upper (D 6) (R 6) [34,192,40,257,65] 13 := by
  apply FastRouting.sound _ _ [34,192,40,257,65] 13 (by decide) (choices 1) [2,4,16] r38637 c38637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24609
  · exact u24610
  · exact u24611

def b38638 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 44 265 82 53 85 149 277), lower := (rows 35 194 44 265 82 32 64 128 256), losses := [] }

theorem u38638 : Upper (D 6) (R 6) [34,192,40,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38639 : Route 9 := (fun mask => (mask,id))

def c38639 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38639 : Upper (D 6) (R 6) [34,192,40,257,68] 13 := by
  apply FastRouting.sound _ _ [34,192,40,257,68] 13 (by decide) (choices 1) [1,2,4,16] r38639 c38639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24612
  · exact u24613
  · exact u24614
  · exact u24615

#print axioms u38639
end Delivery.IrregularNine14.P06
