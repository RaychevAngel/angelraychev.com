import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0325
import IrregularNine14P06C0326
import IrregularNine14P06C0327

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r35640 : Route 9 := (fun mask => (mask,id))

def c35640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35640 : Upper (D 6) (R 6) [34,65,129,18,12] 13 := by
  apply FastRouting.sound _ _ [34,65,129,18,12] 13 (by decide) (choices 1) [4,64,256] r35640 c35640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19537
  · exact u19538
  · exact u19539

def r35641 : Route 9 := (fun mask => (mask,id))

def c35641 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35641 : Upper (D 6) (R 6) [34,65,129,18,36] 13 := by
  apply FastRouting.sound _ _ [34,65,129,18,36] 13 (by decide) (choices 1) [4,8,64,256] r35641 c35641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19540
  · exact u19541
  · exact u19542
  · exact u19543

def b35642 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 67 133 26 56 356 324 452 324), lower := (rows 35 67 133 26 56 32 64 128 256), losses := [] }

theorem u35642 : Upper (D 6) (R 6) [34,65,129,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35643 : Route 9 := (fun mask => (mask,id))

def c35643 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35643 : Upper (D 6) (R 6) [34,65,129,18,68] 13 := by
  apply FastRouting.sound _ _ [34,65,129,18,68] 13 (by decide) (choices 1) [4,8,256] r35643 c35643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19544
  · exact u19545
  · exact u19546

def b35644 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 24, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 67 133 26 88 292 356 420 292), lower := (rows 35 67 133 26 88 32 64 128 256), losses := [] }

theorem u35644 : Upper (D 6) (R 6) [34,65,129,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35645 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 67 133 26 112 300 332 396 268), lower := (rows 35 67 133 26 112 32 64 128 256), losses := [] }

theorem u35645 : Upper (D 6) (R 6) [34,65,129,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35646 : Route 9 := (fun mask => (mask,id))

def c35646 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35646 : Upper (D 6) (R 6) [34,65,129,18,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,18,260] 13 (by decide) (choices 1) [4,8,64] r35646 c35646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19547
  · exact u19548
  · exact u19549

def r35647 : Route 9 := (fun mask => (mask,id))

def c35647 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35647 : Upper (D 6) (R 6) [34,65,129,18,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,18,264] 13 (by decide) (choices 1) [4,64] r35647 c35647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19550
  · exact u19551

def r35648 : Route 9 := (fun mask => (mask,id))

def c35648 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35648 : Upper (D 6) (R 6) [34,65,129,18,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,18,288] 13 (by decide) (choices 1) [4,8,64] r35648 c35648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19552
  · exact u19553
  · exact u19554

def r35649 : Route 9 := (fun mask => (mask,id))

def c35649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35649 : Upper (D 6) (R 6) [34,65,129,18,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,18,320] 13 (by decide) (choices 1) [4,8] r35649 c35649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19555
  · exact u19556

def b35650 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 133 28 28 354 354 482 354), lower := (rows 35 67 133 28 28 32 64 128 256), losses := [] }

theorem u35650 : Upper (D 6) (R 6) [34,65,129,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35651 : PairBound 9 := { available := 332, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 67 133 28 50 364 332 460 332), lower := (rows 35 67 133 28 50 32 64 128 256), losses := [] }

theorem u35651 : Upper (D 6) (R 6) [34,65,129,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35652 : PairBound 9 := { available := 330, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 133 28 52 362 330 458 330), lower := (rows 35 67 133 28 52 32 64 128 256), losses := [] }

theorem u35652 : Upper (D 6) (R 6) [34,65,129,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35653 : Route 9 := (fun mask => (mask,id))

def c35653 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35653 : Upper (D 6) (R 6) [34,65,129,20,40] 13 := by
  apply FastRouting.sound _ _ [34,65,129,20,40] 13 (by decide) (choices 1) [2,4,64,256] r35653 c35653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19557
  · exact u19558
  · exact u19559
  · exact u19560

def b35654 : PairBound 9 := { available := 300, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 133 28 82 300 364 428 300), lower := (rows 35 67 133 28 82 32 64 128 256), losses := [] }

theorem u35654 : Upper (D 6) (R 6) [34,65,129,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35655 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 133 28 84 298 362 426 298), lower := (rows 35 67 133 28 84 32 64 128 256), losses := [] }

theorem u35655 : Upper (D 6) (R 6) [34,65,129,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35656 : Route 9 := (fun mask => (mask,id))

def c35656 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35656 : Upper (D 6) (R 6) [34,65,129,20,72] 13 := by
  apply FastRouting.sound _ _ [34,65,129,20,72] 13 (by decide) (choices 1) [2,4,256] r35656 c35656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19561
  · exact u19562
  · exact u19563

def r35657 : Route 9 := (fun mask => (mask,id))

def c35657 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35657 : Upper (D 6) (R 6) [34,65,129,20,96] 13 := by
  apply FastRouting.sound _ _ [34,65,129,20,96] 13 (by decide) (choices 1) [2,4,8,256] r35657 c35657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19564
  · exact u19565
  · exact u19566
  · exact u19567

def r35658 : Route 9 := (fun mask => (mask,id))

def c35658 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35658 : Upper (D 6) (R 6) [34,65,129,20,258] 13 := by
  apply FastRouting.sound _ _ [34,65,129,20,258] 13 (by decide) (choices 1) [4,8,64] r35658 c35658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19568
  · exact u19569
  · exact u19570

def b35659 : PairBound 9 := { available := 106, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 133 28 276 106 106 234 362), lower := (rows 35 67 133 28 276 32 64 128 256), losses := [] }

theorem u35659 : Upper (D 6) (R 6) [34,65,129,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35660 : Route 9 := (fun mask => (mask,id))

def c35660 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35660 : Upper (D 6) (R 6) [34,65,129,20,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,20,264] 13 (by decide) (choices 1) [2,4,64] r35660 c35660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19571
  · exact u19572
  · exact u19573

def r35661 : Route 9 := (fun mask => (mask,id))

def c35661 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35661 : Upper (D 6) (R 6) [34,65,129,20,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,20,288] 13 (by decide) (choices 1) [2,4,8,64] r35661 c35661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19574
  · exact u19575
  · exact u19576
  · exact u19577

def r35662 : Route 9 := (fun mask => (mask,id))

def c35662 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35662 : Upper (D 6) (R 6) [34,65,129,20,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,20,320] 13 (by decide) (choices 1) [2,4,8] r35662 c35662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19578
  · exact u19579
  · exact u19580

def b35663 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 67 133 42 84 316 348 412 284), lower := (rows 35 67 133 42 84 32 64 128 256), losses := [] }

theorem u35663 : Upper (D 6) (R 6) [34,65,129,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35664 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 67 133 42 88 308 340 404 276), lower := (rows 35 67 133 42 88 32 64 128 256), losses := [] }

theorem u35664 : Upper (D 6) (R 6) [34,65,129,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35665 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 67 133 42 276 124 92 220 348), lower := (rows 35 67 133 42 276 32 64 128 256), losses := [] }

theorem u35665 : Upper (D 6) (R 6) [34,65,129,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35666 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 67 133 42 280 116 84 212 340), lower := (rows 35 67 133 42 280 32 64 128 256), losses := [] }

theorem u35666 : Upper (D 6) (R 6) [34,65,129,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35667 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 67 133 42 336 60 92 156 284), lower := (rows 35 67 133 42 336 32 64 128 256), losses := [] }

theorem u35667 : Upper (D 6) (R 6) [34,65,129,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35668 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 133 44 82 316 348 412 284), lower := (rows 35 67 133 44 82 32 64 128 256), losses := [] }

theorem u35668 : Upper (D 6) (R 6) [34,65,129,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35669 : Route 9 := (fun mask => (mask,id))

def c35669 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35669 : Upper (D 6) (R 6) [34,65,129,36,68] 13 := by
  apply FastRouting.sound _ _ [34,65,129,36,68] 13 (by decide) (choices 1) [2,8,16,256] r35669 c35669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19581
  · exact u19582
  · exact u19583
  · exact u19584

def r35670 : Route 9 := (fun mask => (mask,id))

def c35670 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35670 : Upper (D 6) (R 6) [34,65,129,36,72] 13 := by
  apply FastRouting.sound _ _ [34,65,129,36,72] 13 (by decide) (choices 1) [2,4,16,256] r35670 c35670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19585
  · exact u19586
  · exact u19587
  · exact u19588

def r35671 : Route 9 := (fun mask => (mask,id))

def c35671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35671 : Upper (D 6) (R 6) [34,65,129,36,258] 13 := by
  apply FastRouting.sound _ _ [34,65,129,36,258] 13 (by decide) (choices 1) [4,8,16,64] r35671 c35671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19589
  · exact u19590
  · exact u19591
  · exact u19592

def r35672 : Route 9 := (fun mask => (mask,id))

def c35672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35672 : Upper (D 6) (R 6) [34,65,129,36,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,36,260] 13 (by decide) (choices 1) [2,8,16,64] r35672 c35672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19593
  · exact u19594
  · exact u19595
  · exact u19596

def r35673 : Route 9 := (fun mask => (mask,id))

def c35673 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35673 : Upper (D 6) (R 6) [34,65,129,36,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,36,264] 13 (by decide) (choices 1) [2,4,16,64] r35673 c35673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19597
  · exact u19598
  · exact u19599
  · exact u19600

def r35674 : Route 9 := (fun mask => (mask,id))

def c35674 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35674 : Upper (D 6) (R 6) [34,65,129,36,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,36,320] 13 (by decide) (choices 1) [2,4,8,16] r35674 c35674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19601
  · exact u19602
  · exact u19603
  · exact u19604

def b35675 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 133 56 82 300 332 396 268), lower := (rows 35 67 133 56 82 32 64 128 256), losses := [] }

theorem u35675 : Upper (D 6) (R 6) [34,65,129,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35676 : Route 9 := (fun mask => (mask,id))

def c35676 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35676 : Upper (D 6) (R 6) [34,65,129,48,68] 13 := by
  apply FastRouting.sound _ _ [34,65,129,48,68] 13 (by decide) (choices 1) [2,4,8,256] r35676 c35676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19605
  · exact u19606
  · exact u19607
  · exact u19608

def b35677 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 67 133 56 88 294 326 390 262), lower := (rows 35 67 133 56 88 32 64 128 256), losses := [] }

theorem u35677 : Upper (D 6) (R 6) [34,65,129,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35678 : Route 9 := (fun mask => (mask,id))

def c35678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35678 : Upper (D 6) (R 6) [34,65,129,48,258] 13 := by
  apply FastRouting.sound _ _ [34,65,129,48,258] 13 (by decide) (choices 1) [4,8,64] r35678 c35678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19609
  · exact u19610
  · exact u19611

def r35679 : Route 9 := (fun mask => (mask,id))

def c35679 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35679 : Upper (D 6) (R 6) [34,65,129,48,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,48,260] 13 (by decide) (choices 1) [2,4,8,64] r35679 c35679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19612
  · exact u19613
  · exact u19614
  · exact u19615

def r35680 : Route 9 := (fun mask => (mask,id))

def c35680 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35680 : Upper (D 6) (R 6) [34,65,129,48,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,48,264] 13 (by decide) (choices 1) [2,4,64] r35680 c35680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19616
  · exact u19617
  · exact u19618

def r35681 : Route 9 := (fun mask => (mask,id))

def c35681 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35681 : Upper (D 6) (R 6) [34,65,129,48,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,48,320] 13 (by decide) (choices 1) [2,4,8] r35681 c35681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19619
  · exact u19620
  · exact u19621

def b35682 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 67 133 74 276 60 124 188 316), lower := (rows 35 67 133 74 276 32 64 128 256), losses := [] }

theorem u35682 : Upper (D 6) (R 6) [34,65,129,66,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35683 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 67 133 74 280 52 116 180 308), lower := (rows 35 67 133 74 280 32 64 128 256), losses := [] }

theorem u35683 : Upper (D 6) (R 6) [34,65,129,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35684 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 67 133 74 304 60 92 156 284), lower := (rows 35 67 133 74 304 32 64 128 256), losses := [] }

theorem u35684 : Upper (D 6) (R 6) [34,65,129,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35685 : Route 9 := (fun mask => (mask,id))

def c35685 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35685 : Upper (D 6) (R 6) [34,65,129,68,258] 13 := by
  apply FastRouting.sound _ _ [34,65,129,68,258] 13 (by decide) (choices 1) [4,8,16] r35685 c35685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19622
  · exact u19623
  · exact u19624

def r35686 : Route 9 := (fun mask => (mask,id))

def c35686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35686 : Upper (D 6) (R 6) [34,65,129,68,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,68,260] 13 (by decide) (choices 1) [2,8,16] r35686 c35686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19625
  · exact u19626
  · exact u19627

def r35687 : Route 9 := (fun mask => (mask,id))

def c35687 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35687 : Upper (D 6) (R 6) [34,65,129,68,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,68,264] 13 (by decide) (choices 1) [2,4,16] r35687 c35687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19628
  · exact u19629
  · exact u19630

def r35688 : Route 9 := (fun mask => (mask,id))

def c35688 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35688 : Upper (D 6) (R 6) [34,65,129,68,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,68,288] 13 (by decide) (choices 1) [2,4,8,16] r35688 c35688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19631
  · exact u19632
  · exact u19633
  · exact u19634

def r35689 : Route 9 := (fun mask => (mask,id))

def c35689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35689 : Upper (D 6) (R 6) [34,65,129,80,258] 13 := by
  apply FastRouting.sound _ _ [34,65,129,80,258] 13 (by decide) (choices 1) [4,8] r35689 c35689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19635
  · exact u19636

def r35690 : Route 9 := (fun mask => (mask,id))

def c35690 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35690 : Upper (D 6) (R 6) [34,65,129,80,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,80,260] 13 (by decide) (choices 1) [2,4,8] r35690 c35690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19637
  · exact u19638
  · exact u19639

def r35691 : Route 9 := (fun mask => (mask,id))

def c35691 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35691 : Upper (D 6) (R 6) [34,65,129,80,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,80,264] 13 (by decide) (choices 1) [2,4] r35691 c35691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19640
  · exact u19641

def r35692 : Route 9 := (fun mask => (mask,id))

def c35692 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35692 : Upper (D 6) (R 6) [34,65,129,80,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,80,288] 13 (by decide) (choices 1) [2,4,8] r35692 c35692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19642
  · exact u19643
  · exact u19644

def r35693 : Route 9 := (fun mask => (mask,id))

def c35693 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35693 : Upper (D 6) (R 6) [34,65,129,96,258] 13 := by
  apply FastRouting.sound _ _ [34,65,129,96,258] 13 (by decide) (choices 1) [4,8,16] r35693 c35693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19645
  · exact u19646
  · exact u19647

def r35694 : Route 9 := (fun mask => (mask,id))

def c35694 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35694 : Upper (D 6) (R 6) [34,65,129,96,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,96,260] 13 (by decide) (choices 1) [2,4,8,16] r35694 c35694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19648
  · exact u19649
  · exact u19650
  · exact u19651

def r35695 : Route 9 := (fun mask => (mask,id))

def c35695 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35695 : Upper (D 6) (R 6) [34,65,129,96,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,96,264] 13 (by decide) (choices 1) [2,4,16] r35695 c35695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19652
  · exact u19653
  · exact u19654

def r35696 : Route 9 := (fun mask => (mask,id))

def c35696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u35696 : Upper (D 6) (R 6) [34,65,136,5,6] 13 := by
  apply FastRouting.sound _ _ [34,65,136,5,6] 13 (by decide) (choices 1) [16,64,256] r35696 c35696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19655
  · exact u19656
  · exact u19657

def b35697 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 67 140 13 50 372 340 468 340), lower := (rows 35 67 140 13 50 32 64 128 256), losses := [] }

theorem u35697 : Upper (D 6) (R 6) [34,65,136,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35698 : Route 9 := (fun mask => (mask,id))

def c35698 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u35698 : Upper (D 6) (R 6) [34,65,136,5,36] 13 := by
  apply FastRouting.sound _ _ [34,65,136,5,36] 13 (by decide) (choices 1) [2,16,64,256] r35698 c35698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19658
  · exact u19659
  · exact u19660
  · exact u19661

def b35699 : PairBound 9 := { available := 308, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 140 13 82 308 372 436 308), lower := (rows 35 67 140 13 82 32 64 128 256), losses := [] }

theorem u35699 : Upper (D 6) (R 6) [34,65,136,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u35699
end Delivery.IrregularNine14.P06
