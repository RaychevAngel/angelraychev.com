import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0375
import IrregularNine14P07C0376
import IrregularNine14P07C0377

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36720 : Route 9 := (fun mask => (mask,id))

def c36720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36720 : Upper (D 7) (R 7) [36,72,3,18,288] 13 := by
  apply FastRouting.sound _ _ [36,72,3,18,288] 13 (by decide) (choices 1) [1,64,128] r36720 c36720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22541
  · exact u22542
  · exact u22543

def b36721 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 10, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 7 26 336 161 225 161 417), lower := (rows 37 74 7 26 336 32 64 128 256), losses := [] }

theorem u36721 : Upper (D 7) (R 7) [36,72,3,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36722 : Route 9 := (fun mask => (mask,id))

def c36722 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36722 : Upper (D 7) (R 7) [36,72,3,18,384] 13 := by
  apply FastRouting.sound _ _ [36,72,3,18,384] 13 (by decide) (choices 1) [1,64,128] r36722 c36722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22544
  · exact u22545
  · exact u22546

def b36723 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 16, targets := 192 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 37 74 7 56 19 480 448 448 448), lower := (rows 37 74 7 56 19 32 64 128 256), losses := [] }

theorem u36723 : Upper (D 7) (R 7) [36,72,3,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36724 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 74 7 56 81 418 450 386 386), lower := (rows 37 74 7 56 81 32 64 128 256), losses := [] }

theorem u36724 : Upper (D 7) (R 7) [36,72,3,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36725 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 7 56 82 417 449 385 385), lower := (rows 37 74 7 56 82 32 64 128 256), losses := [] }

theorem u36725 : Upper (D 7) (R 7) [36,72,3,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36726 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 2, region := 464, targets := 32 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(3,0),(4,5)], upper := (rows 37 74 7 56 145 482 450 450 450), lower := (rows 37 74 7 56 145 32 64 128 256), losses := [] }

theorem u36726 : Upper (D 7) (R 7) [36,72,3,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36727 : Route 9 := (fun mask => (mask,id))

def c36727 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u36727 : Upper (D 7) (R 7) [36,72,3,48,130] 13 := by
  apply FastRouting.sound _ _ [36,72,3,48,130] 13 (by decide) (choices 1) [1,64,128,256] r36727 c36727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22547
  · exact u22548
  · exact u22549
  · exact u22550

def r36728 : Route 9 := (fun mask => (mask,id))

def c36728 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36728 : Upper (D 7) (R 7) [36,72,3,48,192] 13 := by
  apply FastRouting.sound _ _ [36,72,3,48,192] 13 (by decide) (choices 1) [1,2,128,256] r36728 c36728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22551
  · exact u22552
  · exact u22553
  · exact u22554

def b36729 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 2, region := 464, targets := 32 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(3,0),(4,5)], upper := (rows 37 74 7 56 273 226 194 194 450), lower := (rows 37 74 7 56 273 32 64 128 256), losses := [] }

theorem u36729 : Upper (D 7) (R 7) [36,72,3,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36730 : Route 9 := (fun mask => (mask,id))

def c36730 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36730 : Upper (D 7) (R 7) [36,72,3,48,258] 13 := by
  apply FastRouting.sound _ _ [36,72,3,48,258] 13 (by decide) (choices 1) [1,64,128] r36730 c36730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22555
  · exact u22556
  · exact u22557

def r36731 : Route 9 := (fun mask => (mask,id))

def c36731 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36731 : Upper (D 7) (R 7) [36,72,3,48,320] 13 := by
  apply FastRouting.sound _ _ [36,72,3,48,320] 13 (by decide) (choices 1) [1,2,128] r36731 c36731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22558
  · exact u22559
  · exact u22560

def r36732 : Route 9 := (fun mask => (mask,id))

def c36732 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36732 : Upper (D 7) (R 7) [36,72,3,48,384] 13 := by
  apply FastRouting.sound _ _ [36,72,3,48,384] 13 (by decide) (choices 1) [1,2,64,128] r36732 c36732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22561
  · exact u22562
  · exact u22563
  · exact u22564

def b36733 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 137 50 496 464 464 464), lower := (rows 37 74 7 137 50 32 64 128 256), losses := [] }

theorem u36733 : Upper (D 7) (R 7) [36,72,3,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36734 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 429, targets := 64 },{ cop := 1, region := 16, targets := 32 }], pairs := [(0,6),(2,6),(3,6),(4,5)], upper := (rows 37 74 7 137 82 432 496 432 432), lower := (rows 37 74 7 137 82 32 64 128 256), losses := [] }

theorem u36734 : Upper (D 7) (R 7) [36,72,3,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36735 : Route 9 := (fun mask => (mask,id))

def c36735 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u36735 : Upper (D 7) (R 7) [36,72,3,129,96] 13 := by
  apply FastRouting.sound _ _ [36,72,3,129,96] 13 (by decide) (choices 1) [2,16,128,256] r36735 c36735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22565
  · exact u22566
  · exact u22567
  · exact u22568

def b36736 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 7 137 146 368 368 496 368), lower := (rows 37 74 7 137 146 32 64 128 256), losses := [] }

theorem u36736 : Upper (D 7) (R 7) [36,72,3,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36737 : Route 9 := (fun mask => (mask,id))

def c36737 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u36737 : Upper (D 7) (R 7) [36,72,3,129,160] 13 := by
  apply FastRouting.sound _ _ [36,72,3,129,160] 13 (by decide) (choices 1) [2,16,64,256] r36737 c36737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22569
  · exact u22570
  · exact u22571
  · exact u22572

def r36738 : Route 9 := (fun mask => (mask,id))

def c36738 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36738 : Upper (D 7) (R 7) [36,72,3,129,192] 13 := by
  apply FastRouting.sound _ _ [36,72,3,129,192] 13 (by decide) (choices 1) [2,16,256] r36738 c36738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22573
  · exact u22574
  · exact u22575

def r36739 : Route 9 := (fun mask => (mask,id))

def c36739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36739 : Upper (D 7) (R 7) [36,72,3,129,258] 13 := by
  apply FastRouting.sound _ _ [36,72,3,129,258] 13 (by decide) (choices 1) [16,64,128] r36739 c36739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22576
  · exact u22577
  · exact u22578

def r36740 : Route 9 := (fun mask => (mask,id))

def c36740 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36740 : Upper (D 7) (R 7) [36,72,3,129,288] 13 := by
  apply FastRouting.sound _ _ [36,72,3,129,288] 13 (by decide) (choices 1) [2,16,64,128] r36740 c36740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22579
  · exact u22580
  · exact u22581
  · exact u22582

def r36741 : Route 9 := (fun mask => (mask,id))

def c36741 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36741 : Upper (D 7) (R 7) [36,72,3,129,320] 13 := by
  apply FastRouting.sound _ _ [36,72,3,129,320] 13 (by decide) (choices 1) [2,16,128] r36741 c36741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22583
  · exact u22584
  · exact u22585

def r36742 : Route 9 := (fun mask => (mask,id))

def c36742 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36742 : Upper (D 7) (R 7) [36,72,3,129,384] 13 := by
  apply FastRouting.sound _ _ [36,72,3,129,384] 13 (by decide) (choices 1) [2,16,64] r36742 c36742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22586
  · exact u22587
  · exact u22588

def b36743 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 37 74 7 138 49 496 464 464 464), lower := (rows 37 74 7 138 49 32 64 128 256), losses := [] }

theorem u36743 : Upper (D 7) (R 7) [36,72,3,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36744 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 74 7 138 81 432 496 432 432), lower := (rows 37 74 7 138 81 32 64 128 256), losses := [] }

theorem u36744 : Upper (D 7) (R 7) [36,72,3,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36745 : Route 9 := (fun mask => (mask,id))

def c36745 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u36745 : Upper (D 7) (R 7) [36,72,3,130,96] 13 := by
  apply FastRouting.sound _ _ [36,72,3,130,96] 13 (by decide) (choices 1) [1,16,128,256] r36745 c36745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22589
  · exact u22590
  · exact u22591
  · exact u22592

def b36746 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 74 7 138 145 368 368 496 368), lower := (rows 37 74 7 138 145 32 64 128 256), losses := [] }

theorem u36746 : Upper (D 7) (R 7) [36,72,3,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36747 : Route 9 := (fun mask => (mask,id))

def c36747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u36747 : Upper (D 7) (R 7) [36,72,3,130,160] 13 := by
  apply FastRouting.sound _ _ [36,72,3,130,160] 13 (by decide) (choices 1) [1,16,64,256] r36747 c36747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22593
  · exact u22594
  · exact u22595
  · exact u22596

def b36748 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 7 138 208 305 369 433 305), lower := (rows 37 74 7 138 208 32 64 128 256), losses := [] }

theorem u36748 : Upper (D 7) (R 7) [36,72,3,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36749 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 74 7 138 273 240 240 240 496), lower := (rows 37 74 7 138 273 32 64 128 256), losses := [] }

theorem u36749 : Upper (D 7) (R 7) [36,72,3,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36750 : Route 9 := (fun mask => (mask,id))

def c36750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36750 : Upper (D 7) (R 7) [36,72,3,130,288] 13 := by
  apply FastRouting.sound _ _ [36,72,3,130,288] 13 (by decide) (choices 1) [1,16,64,128] r36750 c36750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22597
  · exact u22598
  · exact u22599
  · exact u22600

def r36751 : Route 9 := (fun mask => (mask,id))

def c36751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36751 : Upper (D 7) (R 7) [36,72,3,130,320] 13 := by
  apply FastRouting.sound _ _ [36,72,3,130,320] 13 (by decide) (choices 1) [1,16,128] r36751 c36751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22601
  · exact u22602
  · exact u22603

def r36752 : Route 9 := (fun mask => (mask,id))

def c36752 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36752 : Upper (D 7) (R 7) [36,72,3,130,384] 13 := by
  apply FastRouting.sound _ _ [36,72,3,130,384] 13 (by decide) (choices 1) [1,16,64] r36752 c36752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22604
  · exact u22605
  · exact u22606

def b36753 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 16, targets := 224 },{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 74 7 152 19 480 480 480 480), lower := (rows 37 74 7 152 19 32 64 128 256), losses := [] }

theorem u36753 : Upper (D 7) (R 7) [36,72,3,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36754 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 7 152 49 482 450 450 450), lower := (rows 37 74 7 152 49 32 64 128 256), losses := [] }

theorem u36754 : Upper (D 7) (R 7) [36,72,3,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36755 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 152 50 481 449 449 449), lower := (rows 37 74 7 152 50 32 64 128 256), losses := [] }

theorem u36755 : Upper (D 7) (R 7) [36,72,3,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36756 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 74 7 152 81 418 482 418 418), lower := (rows 37 74 7 152 81 32 64 128 256), losses := [] }

theorem u36756 : Upper (D 7) (R 7) [36,72,3,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36757 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 7 152 82 417 481 417 417), lower := (rows 37 74 7 152 82 32 64 128 256), losses := [] }

theorem u36757 : Upper (D 7) (R 7) [36,72,3,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36758 : Route 9 := (fun mask => (mask,id))

def c36758 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36758 : Upper (D 7) (R 7) [36,72,3,144,96] 13 := by
  apply FastRouting.sound _ _ [36,72,3,144,96] 13 (by decide) (choices 1) [1,2,128,256] r36758 c36758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22607
  · exact u22608
  · exact u22609
  · exact u22610

def b36759 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 37 74 7 152 145 354 354 482 354), lower := (rows 37 74 7 152 145 32 64 128 256), losses := [] }

theorem u36759 : Upper (D 7) (R 7) [36,72,3,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36760 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 74 7 152 146 353 353 481 353), lower := (rows 37 74 7 152 146 32 64 128 256), losses := [] }

theorem u36760 : Upper (D 7) (R 7) [36,72,3,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36761 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 74 7 152 176 355 323 451 323), lower := (rows 37 74 7 152 176 32 64 128 256), losses := [] }

theorem u36761 : Upper (D 7) (R 7) [36,72,3,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36762 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 7 152 208 291 355 419 291), lower := (rows 37 74 7 152 208 32 64 128 256), losses := [] }

theorem u36762 : Upper (D 7) (R 7) [36,72,3,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36763 : Route 9 := (fun mask => (mask,id))

def c36763 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36763 : Upper (D 7) (R 7) [36,72,3,144,257] 13 := by
  apply FastRouting.sound _ _ [36,72,3,144,257] 13 (by decide) (choices 1) [2,64,128] r36763 c36763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22611
  · exact u22612
  · exact u22613

def r36764 : Route 9 := (fun mask => (mask,id))

def c36764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36764 : Upper (D 7) (R 7) [36,72,3,144,258] 13 := by
  apply FastRouting.sound _ _ [36,72,3,144,258] 13 (by decide) (choices 1) [1,64,128] r36764 c36764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22614
  · exact u22615
  · exact u22616

def r36765 : Route 9 := (fun mask => (mask,id))

def c36765 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36765 : Upper (D 7) (R 7) [36,72,3,144,288] 13 := by
  apply FastRouting.sound _ _ [36,72,3,144,288] 13 (by decide) (choices 1) [1,2,64,128] r36765 c36765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22617
  · exact u22618
  · exact u22619
  · exact u22620

def r36766 : Route 9 := (fun mask => (mask,id))

def c36766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36766 : Upper (D 7) (R 7) [36,72,3,144,320] 13 := by
  apply FastRouting.sound _ _ [36,72,3,144,320] 13 (by decide) (choices 1) [1,2,128] r36766 c36766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22621
  · exact u22622
  · exact u22623

def b36767 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 74 7 152 400 99 99 227 355), lower := (rows 37 74 7 152 400 32 64 128 256), losses := [] }

theorem u36767 : Upper (D 7) (R 7) [36,72,3,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36768 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 16, targets := 192 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 37 74 7 168 19 496 464 464 464), lower := (rows 37 74 7 168 19 32 64 128 256), losses := [] }

theorem u36768 : Upper (D 7) (R 7) [36,72,3,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36769 : Route 9 := (fun mask => (mask,id))

def c36769 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u36769 : Upper (D 7) (R 7) [36,72,3,160,65] 13 := by
  apply FastRouting.sound _ _ [36,72,3,160,65] 13 (by decide) (choices 1) [2,16,128,256] r36769 c36769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22624
  · exact u22625
  · exact u22626
  · exact u22627

def b36770 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 7 168 82 433 465 401 401), lower := (rows 37 74 7 168 82 32 64 128 256), losses := [] }

theorem u36770 : Upper (D 7) (R 7) [36,72,3,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36771 : Route 9 := (fun mask => (mask,id))

def c36771 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u36771 : Upper (D 7) (R 7) [36,72,3,160,129] 13 := by
  apply FastRouting.sound _ _ [36,72,3,160,129] 13 (by decide) (choices 1) [2,16,64,256] r36771 c36771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22628
  · exact u22629
  · exact u22630
  · exact u22631

def r36772 : Route 9 := (fun mask => (mask,id))

def c36772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u36772 : Upper (D 7) (R 7) [36,72,3,160,130] 13 := by
  apply FastRouting.sound _ _ [36,72,3,160,130] 13 (by decide) (choices 1) [1,16,64,256] r36772 c36772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22632
  · exact u22633
  · exact u22634
  · exact u22635

def r36773 : Route 9 := (fun mask => (mask,id))

def c36773 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36773 : Upper (D 7) (R 7) [36,72,3,160,192] 13 := by
  apply FastRouting.sound _ _ [36,72,3,160,192] 13 (by decide) (choices 1) [1,2,16,256] r36773 c36773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22636
  · exact u22637
  · exact u22638
  · exact u22639

def r36774 : Route 9 := (fun mask => (mask,id))

def c36774 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36774 : Upper (D 7) (R 7) [36,72,3,160,257] 13 := by
  apply FastRouting.sound _ _ [36,72,3,160,257] 13 (by decide) (choices 1) [2,16,64,128] r36774 c36774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22640
  · exact u22641
  · exact u22642
  · exact u22643

def r36775 : Route 9 := (fun mask => (mask,id))

def c36775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36775 : Upper (D 7) (R 7) [36,72,3,160,258] 13 := by
  apply FastRouting.sound _ _ [36,72,3,160,258] 13 (by decide) (choices 1) [1,16,64,128] r36775 c36775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22644
  · exact u22645
  · exact u22646
  · exact u22647

def r36776 : Route 9 := (fun mask => (mask,id))

def c36776 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36776 : Upper (D 7) (R 7) [36,72,3,160,320] 13 := by
  apply FastRouting.sound _ _ [36,72,3,160,320] 13 (by decide) (choices 1) [1,2,16,128] r36776 c36776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22648
  · exact u22649
  · exact u22650
  · exact u22651

def r36777 : Route 9 := (fun mask => (mask,id))

def c36777 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36777 : Upper (D 7) (R 7) [36,72,3,160,384] 13 := by
  apply FastRouting.sound _ _ [36,72,3,160,384] 13 (by decide) (choices 1) [1,2,16,64] r36777 c36777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22652
  · exact u22653
  · exact u22654
  · exact u22655

def b36778 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 265 50 240 208 208 464), lower := (rows 37 74 7 265 50 32 64 128 256), losses := [] }

theorem u36778 : Upper (D 7) (R 7) [36,72,3,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36779 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 429, targets := 64 },{ cop := 1, region := 16, targets := 32 }], pairs := [(0,6),(2,6),(3,6),(4,5)], upper := (rows 37 74 7 265 82 176 240 176 432), lower := (rows 37 74 7 265 82 32 64 128 256), losses := [] }

theorem u36779 : Upper (D 7) (R 7) [36,72,3,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u36779
end Delivery.IrregularNine14.P07
