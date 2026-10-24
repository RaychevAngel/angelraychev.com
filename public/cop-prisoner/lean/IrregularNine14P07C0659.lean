import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0460
import IrregularNine14P07C0461
import IrregularNine14P07C0462

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39540 : Route 9 := (fun mask => (mask,id))

def c39540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39540 : Upper (D 7) (R 7) [36,320,129,17,130] 13 := by
  apply FastRouting.sound _ _ [36,320,129,17,130] 13 (by decide) (choices 1) [2,8,64] r39540 c39540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27634
  · exact u27635
  · exact u27636

def b39541 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 322 133 25 152 98 98 226 354), lower := (rows 37 322 133 25 152 32 64 128 256), losses := [] }

theorem u39541 : Upper (D 7) (R 7) [36,320,129,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39542 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 25 176 106 74 202 330), lower := (rows 37 322 133 25 176 32 64 128 256), losses := [] }

theorem u39542 : Upper (D 7) (R 7) [36,320,129,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39543 : Route 9 := (fun mask => (mask,id))

def c39543 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39543 : Upper (D 7) (R 7) [36,320,129,17,192] 13 := by
  apply FastRouting.sound _ _ [36,320,129,17,192] 13 (by decide) (choices 1) [2,8] r39543 c39543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27637
  · exact u27638

def b39544 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 322 133 26 26 225 225 225 481), lower := (rows 37 322 133 26 26 32 64 128 256), losses := [] }

theorem u39544 : Upper (D 7) (R 7) [36,320,129,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39545 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 133 26 49 234 202 202 458), lower := (rows 37 322 133 26 49 32 64 128 256), losses := [] }

theorem u39545 : Upper (D 7) (R 7) [36,320,129,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39546 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 322 133 26 50 233 201 201 457), lower := (rows 37 322 133 26 50 32 64 128 256), losses := [] }

theorem u39546 : Upper (D 7) (R 7) [36,320,129,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39547 : Route 9 := (fun mask => (mask,id))

def c39547 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39547 : Upper (D 7) (R 7) [36,320,129,18,40] 13 := by
  apply FastRouting.sound _ _ [36,320,129,18,40] 13 (by decide) (choices 1) [1,2,64,128] r39547 c39547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27639
  · exact u27640
  · exact u27641
  · exact u27642

def b39548 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 322 133 26 81 170 234 170 426), lower := (rows 37 322 133 26 81 32 64 128 256), losses := [] }

theorem u39548 : Upper (D 7) (R 7) [36,320,129,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39549 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 322 133 26 82 169 233 169 425), lower := (rows 37 322 133 26 82 32 64 128 256), losses := [] }

theorem u39549 : Upper (D 7) (R 7) [36,320,129,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39550 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 322 133 26 88 163 227 163 419), lower := (rows 37 322 133 26 88 32 64 128 256), losses := [] }

theorem u39550 : Upper (D 7) (R 7) [36,320,129,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39551 : Route 9 := (fun mask => (mask,id))

def c39551 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39551 : Upper (D 7) (R 7) [36,320,129,18,96] 13 := by
  apply FastRouting.sound _ _ [36,320,129,18,96] 13 (by decide) (choices 1) [1,2,8,128] r39551 c39551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27643
  · exact u27644
  · exact u27645
  · exact u27646

def b39552 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 37 322 133 26 145 106 106 234 362), lower := (rows 37 322 133 26 145 32 64 128 256), losses := [] }

theorem u39552 : Upper (D 7) (R 7) [36,320,129,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39553 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 322 133 26 146 105 105 233 361), lower := (rows 37 322 133 26 146 32 64 128 256), losses := [] }

theorem u39553 : Upper (D 7) (R 7) [36,320,129,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39554 : Route 9 := (fun mask => (mask,id))

def c39554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39554 : Upper (D 7) (R 7) [36,320,129,18,136] 13 := by
  apply FastRouting.sound _ _ [36,320,129,18,136] 13 (by decide) (choices 1) [1,2,64] r39554 c39554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27647
  · exact u27648
  · exact u27649

def b39555 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 26 176 107 75 203 331), lower := (rows 37 322 133 26 176 32 64 128 256), losses := [] }

theorem u39555 : Upper (D 7) (R 7) [36,320,129,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39556 : Route 9 := (fun mask => (mask,id))

def c39556 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39556 : Upper (D 7) (R 7) [36,320,129,18,192] 13 := by
  apply FastRouting.sound _ _ [36,320,129,18,192] 13 (by decide) (choices 1) [1,2,8] r39556 c39556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27650
  · exact u27651
  · exact u27652

def b39557 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 133 41 88 178 210 146 402), lower := (rows 37 322 133 41 88 32 64 128 256), losses := [] }

theorem u39557 : Upper (D 7) (R 7) [36,320,129,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39558 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 133 41 146 122 90 218 346), lower := (rows 37 322 133 41 146 32 64 128 256), losses := [] }

theorem u39558 : Upper (D 7) (R 7) [36,320,129,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39559 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 133 41 152 114 82 210 338), lower := (rows 37 322 133 41 152 32 64 128 256), losses := [] }

theorem u39559 : Upper (D 7) (R 7) [36,320,129,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39560 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 133 41 208 58 90 154 282), lower := (rows 37 322 133 41 208 32 64 128 256), losses := [] }

theorem u39560 : Upper (D 7) (R 7) [36,320,129,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39561 : Route 9 := (fun mask => (mask,id))

def c39561 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39561 : Upper (D 7) (R 7) [36,320,129,34,65] 13 := by
  apply FastRouting.sound _ _ [36,320,129,34,65] 13 (by decide) (choices 1) [2,8,16,128] r39561 c39561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27653
  · exact u27654
  · exact u27655
  · exact u27656

def b39562 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 133 42 82 185 217 153 409), lower := (rows 37 322 133 42 82 32 64 128 256), losses := [] }

theorem u39562 : Upper (D 7) (R 7) [36,320,129,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39563 : Route 9 := (fun mask => (mask,id))

def c39563 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39563 : Upper (D 7) (R 7) [36,320,129,34,72] 13 := by
  apply FastRouting.sound _ _ [36,320,129,34,72] 13 (by decide) (choices 1) [1,2,16,128] r39563 c39563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27657
  · exact u27658
  · exact u27659
  · exact u27660

def b39564 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 37 322 133 42 145 122 90 218 346), lower := (rows 37 322 133 42 145 32 64 128 256), losses := [] }

theorem u39564 : Upper (D 7) (R 7) [36,320,129,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39565 : Route 9 := (fun mask => (mask,id))

def c39565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39565 : Upper (D 7) (R 7) [36,320,129,34,130] 13 := by
  apply FastRouting.sound _ _ [36,320,129,34,130] 13 (by decide) (choices 1) [1,8,16,64] r39565 c39565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27661
  · exact u27662
  · exact u27663
  · exact u27664

def r39566 : Route 9 := (fun mask => (mask,id))

def c39566 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39566 : Upper (D 7) (R 7) [36,320,129,34,136] 13 := by
  apply FastRouting.sound _ _ [36,320,129,34,136] 13 (by decide) (choices 1) [1,2,16,64] r39566 c39566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27665
  · exact u27666
  · exact u27667
  · exact u27668

def r39567 : Route 9 := (fun mask => (mask,id))

def c39567 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39567 : Upper (D 7) (R 7) [36,320,129,34,192] 13 := by
  apply FastRouting.sound _ _ [36,320,129,34,192] 13 (by decide) (choices 1) [1,2,8,16] r39567 c39567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27669
  · exact u27670
  · exact u27671
  · exact u27672

def r39568 : Route 9 := (fun mask => (mask,id))

def c39568 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39568 : Upper (D 7) (R 7) [36,320,129,48,65] 13 := by
  apply FastRouting.sound _ _ [36,320,129,48,65] 13 (by decide) (choices 1) [2,8,128] r39568 c39568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27673
  · exact u27674
  · exact u27675

def b39569 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 133 56 82 171 203 139 395), lower := (rows 37 322 133 56 82 32 64 128 256), losses := [] }

theorem u39569 : Upper (D 7) (R 7) [36,320,129,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39570 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(2,6)], upper := (rows 37 322 133 56 88 163 195 131 387), lower := (rows 37 322 133 56 88 32 64 128 256), losses := [] }

theorem u39570 : Upper (D 7) (R 7) [36,320,129,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39571 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 37 322 133 56 145 106 74 202 330), lower := (rows 37 322 133 56 145 32 64 128 256), losses := [] }

theorem u39571 : Upper (D 7) (R 7) [36,320,129,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39572 : Route 9 := (fun mask => (mask,id))

def c39572 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39572 : Upper (D 7) (R 7) [36,320,129,48,130] 13 := by
  apply FastRouting.sound _ _ [36,320,129,48,130] 13 (by decide) (choices 1) [1,2,8,64] r39572 c39572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27676
  · exact u27677
  · exact u27678
  · exact u27679

def b39573 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,5)], upper := (rows 37 322 133 56 152 99 67 195 323), lower := (rows 37 322 133 56 152 32 64 128 256), losses := [] }

theorem u39573 : Upper (D 7) (R 7) [36,320,129,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39574 : Route 9 := (fun mask => (mask,id))

def c39574 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39574 : Upper (D 7) (R 7) [36,320,129,48,192] 13 := by
  apply FastRouting.sound _ _ [36,320,129,48,192] 13 (by decide) (choices 1) [1,2,8] r39574 c39574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27680
  · exact u27681
  · exact u27682

def r39575 : Route 9 := (fun mask => (mask,id))

def c39575 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39575 : Upper (D 7) (R 7) [36,320,129,65,130] 13 := by
  apply FastRouting.sound _ _ [36,320,129,65,130] 13 (by decide) (choices 1) [2,8,16] r39575 c39575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27683
  · exact u27684
  · exact u27685

def r39576 : Route 9 := (fun mask => (mask,id))

def c39576 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39576 : Upper (D 7) (R 7) [36,320,129,65,136] 13 := by
  apply FastRouting.sound _ _ [36,320,129,65,136] 13 (by decide) (choices 1) [2,16] r39576 c39576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27686
  · exact u27687

def b39577 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 73 176 58 90 154 282), lower := (rows 37 322 133 73 176 32 64 128 256), losses := [] }

theorem u39577 : Upper (D 7) (R 7) [36,320,129,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39578 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 133 74 146 57 121 185 313), lower := (rows 37 322 133 74 146 32 64 128 256), losses := [] }

theorem u39578 : Upper (D 7) (R 7) [36,320,129,66,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39579 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 133 74 152 51 115 179 307), lower := (rows 37 322 133 74 152 32 64 128 256), losses := [] }

theorem u39579 : Upper (D 7) (R 7) [36,320,129,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39580 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 37 322 133 88 145 42 106 170 298), lower := (rows 37 322 133 88 145 32 64 128 256), losses := [] }

theorem u39580 : Upper (D 7) (R 7) [36,320,129,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39581 : Route 9 := (fun mask => (mask,id))

def c39581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39581 : Upper (D 7) (R 7) [36,320,129,80,130] 13 := by
  apply FastRouting.sound _ _ [36,320,129,80,130] 13 (by decide) (choices 1) [1,2,8] r39581 c39581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27688
  · exact u27689
  · exact u27690

def b39582 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(2,6)], upper := (rows 37 322 133 88 152 35 99 163 291), lower := (rows 37 322 133 88 152 32 64 128 256), losses := [] }

theorem u39582 : Upper (D 7) (R 7) [36,320,129,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39583 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 88 176 43 75 139 267), lower := (rows 37 322 133 88 176 32 64 128 256), losses := [] }

theorem u39583 : Upper (D 7) (R 7) [36,320,129,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39584 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 37 322 133 104 145 58 90 154 282), lower := (rows 37 322 133 104 145 32 64 128 256), losses := [] }

theorem u39584 : Upper (D 7) (R 7) [36,320,129,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39584 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39585 : Route 9 := (fun mask => (mask,id))

def c39585 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39585 : Upper (D 7) (R 7) [36,320,129,96,130] 13 := by
  apply FastRouting.sound _ _ [36,320,129,96,130] 13 (by decide) (choices 1) [1,2,8,16] r39585 c39585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27691
  · exact u27692
  · exact u27693
  · exact u27694

def r39586 : Route 9 := (fun mask => (mask,id))

def c39586 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39586 : Upper (D 7) (R 7) [36,320,129,96,136] 13 := by
  apply FastRouting.sound _ _ [36,320,129,96,136] 13 (by decide) (choices 1) [1,2,16] r39586 c39586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27695
  · exact u27696
  · exact u27697

def b39587 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 482, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 37 322 134 11 25 240 240 240 496), lower := (rows 37 322 134 11 25 32 64 128 256), losses := [] }

theorem u39587 : Upper (D 7) (R 7) [36,320,130,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39588 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 134 11 49 248 216 216 472), lower := (rows 37 322 134 11 49 32 64 128 256), losses := [] }

theorem u39588 : Upper (D 7) (R 7) [36,320,130,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39589 : Route 9 := (fun mask => (mask,id))

def c39589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39589 : Upper (D 7) (R 7) [36,320,130,3,40] 13 := by
  apply FastRouting.sound _ _ [36,320,130,3,40] 13 (by decide) (choices 1) [1,16,64,128] r39589 c39589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27698
  · exact u27699
  · exact u27700
  · exact u27701

def r39590 : Route 9 := (fun mask => (mask,id))

def c39590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39590 : Upper (D 7) (R 7) [36,320,130,3,65] 13 := by
  apply FastRouting.sound _ _ [36,320,130,3,65] 13 (by decide) (choices 1) [8,16,128] r39590 c39590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27702
  · exact u27703
  · exact u27704

def r39591 : Route 9 := (fun mask => (mask,id))

def c39591 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39591 : Upper (D 7) (R 7) [36,320,130,3,72] 13 := by
  apply FastRouting.sound _ _ [36,320,130,3,72] 13 (by decide) (choices 1) [1,16,128] r39591 c39591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27705
  · exact u27706
  · exact u27707

def r39592 : Route 9 := (fun mask => (mask,id))

def c39592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39592 : Upper (D 7) (R 7) [36,320,130,3,96] 13 := by
  apply FastRouting.sound _ _ [36,320,130,3,96] 13 (by decide) (choices 1) [1,8,16,128] r39592 c39592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27708
  · exact u27709
  · exact u27710
  · exact u27711

def r39593 : Route 9 := (fun mask => (mask,id))

def c39593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39593 : Upper (D 7) (R 7) [36,320,130,3,129] 13 := by
  apply FastRouting.sound _ _ [36,320,130,3,129] 13 (by decide) (choices 1) [8,16,64] r39593 c39593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27712
  · exact u27713
  · exact u27714

def r39594 : Route 9 := (fun mask => (mask,id))

def c39594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39594 : Upper (D 7) (R 7) [36,320,130,3,136] 13 := by
  apply FastRouting.sound _ _ [36,320,130,3,136] 13 (by decide) (choices 1) [1,16,64] r39594 c39594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27715
  · exact u27716
  · exact u27717

def r39595 : Route 9 := (fun mask => (mask,id))

def c39595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39595 : Upper (D 7) (R 7) [36,320,130,3,160] 13 := by
  apply FastRouting.sound _ _ [36,320,130,3,160] 13 (by decide) (choices 1) [1,8,16,64] r39595 c39595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27718
  · exact u27719
  · exact u27720
  · exact u27721

def r39596 : Route 9 := (fun mask => (mask,id))

def c39596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39596 : Upper (D 7) (R 7) [36,320,130,3,192] 13 := by
  apply FastRouting.sound _ _ [36,320,130,3,192] 13 (by decide) (choices 1) [1,8,16] r39596 c39596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27722
  · exact u27723
  · exact u27724

def b39597 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 322 134 25 25 226 226 226 482), lower := (rows 37 322 134 25 25 32 64 128 256), losses := [] }

theorem u39597 : Upper (D 7) (R 7) [36,320,130,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39598 : Route 9 := (fun mask => (mask,id))

def c39598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39598 : Upper (D 7) (R 7) [36,320,130,17,10] 13 := by
  apply FastRouting.sound _ _ [36,320,130,17,10] 13 (by decide) (choices 1) [1,64,128] r39598 c39598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27725
  · exact u27726
  · exact u27727

def b39599 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 322 134 25 49 234 202 202 458), lower := (rows 37 322 134 25 49 32 64 128 256), losses := [] }

theorem u39599 : Upper (D 7) (R 7) [36,320,130,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u39599
end Delivery.IrregularNine14.P07
