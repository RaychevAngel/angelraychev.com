import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0462
import IrregularNine14P07C0463

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39600 : Route 9 := (fun mask => (mask,id))

def c39600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39600 : Upper (D 7) (R 7) [36,320,130,17,34] 13 := by
  apply FastRouting.sound _ _ [36,320,130,17,34] 13 (by decide) (choices 1) [1,8,64,128] r39600 c39600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27728
  · exact u27729
  · exact u27730
  · exact u27731

def b39601 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 322 134 25 56 227 195 195 451), lower := (rows 37 322 134 25 56 32 64 128 256), losses := [] }

theorem u39601 : Upper (D 7) (R 7) [36,320,130,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39602 : PairBound 9 := { available := 170, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 322 134 25 81 170 234 170 426), lower := (rows 37 322 134 25 81 32 64 128 256), losses := [] }

theorem u39602 : Upper (D 7) (R 7) [36,320,130,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39603 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 134 25 82 169 233 169 425), lower := (rows 37 322 134 25 82 32 64 128 256), losses := [] }

theorem u39603 : Upper (D 7) (R 7) [36,320,130,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39604 : Route 9 := (fun mask => (mask,id))

def c39604 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39604 : Upper (D 7) (R 7) [36,320,130,17,72] 13 := by
  apply FastRouting.sound _ _ [36,320,130,17,72] 13 (by decide) (choices 1) [1,2,128] r39604 c39604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27732
  · exact u27733
  · exact u27734

def r39605 : Route 9 := (fun mask => (mask,id))

def c39605 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39605 : Upper (D 7) (R 7) [36,320,130,17,96] 13 := by
  apply FastRouting.sound _ _ [36,320,130,17,96] 13 (by decide) (choices 1) [1,2,8,128] r39605 c39605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27735
  · exact u27736
  · exact u27737
  · exact u27738

def b39606 : PairBound 9 := { available := 106, camps := [{ cop := 4, region := 8, targets := 98 },{ cop := 3, region := 354, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 134 25 145 106 106 234 362), lower := (rows 37 322 134 25 145 32 64 128 256), losses := [] }

theorem u39606 : Upper (D 7) (R 7) [36,320,130,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39607 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 37 322 134 25 146 105 105 233 361), lower := (rows 37 322 134 25 146 32 64 128 256), losses := [] }

theorem u39607 : Upper (D 7) (R 7) [36,320,130,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39608 : Route 9 := (fun mask => (mask,id))

def c39608 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39608 : Upper (D 7) (R 7) [36,320,130,17,136] 13 := by
  apply FastRouting.sound _ _ [36,320,130,17,136] 13 (by decide) (choices 1) [1,2,64] r39608 c39608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27739
  · exact u27740
  · exact u27741

def r39609 : Route 9 := (fun mask => (mask,id))

def c39609 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39609 : Upper (D 7) (R 7) [36,320,130,17,160] 13 := by
  apply FastRouting.sound _ _ [36,320,130,17,160] 13 (by decide) (choices 1) [1,2,8,64] r39609 c39609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27742
  · exact u27743
  · exact u27744
  · exact u27745

def r39610 : Route 9 := (fun mask => (mask,id))

def c39610 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39610 : Upper (D 7) (R 7) [36,320,130,17,192] 13 := by
  apply FastRouting.sound _ _ [36,320,130,17,192] 13 (by decide) (choices 1) [1,2,8] r39610 c39610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27746
  · exact u27747
  · exact u27748

def b39611 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 134 26 49 233 201 201 457), lower := (rows 37 322 134 26 49 32 64 128 256), losses := [] }

theorem u39611 : Upper (D 7) (R 7) [36,320,130,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39612 : Route 9 := (fun mask => (mask,id))

def c39612 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39612 : Upper (D 7) (R 7) [36,320,130,18,40] 13 := by
  apply FastRouting.sound _ _ [36,320,130,18,40] 13 (by decide) (choices 1) [1,64,128] r39612 c39612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27749
  · exact u27750
  · exact u27751

def r39613 : Route 9 := (fun mask => (mask,id))

def c39613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39613 : Upper (D 7) (R 7) [36,320,130,18,65] 13 := by
  apply FastRouting.sound _ _ [36,320,130,18,65] 13 (by decide) (choices 1) [1,8,128] r39613 c39613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27752
  · exact u27753
  · exact u27754

def b39614 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 322 134 26 88 161 225 161 417), lower := (rows 37 322 134 26 88 32 64 128 256), losses := [] }

theorem u39614 : Upper (D 7) (R 7) [36,320,130,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39615 : Route 9 := (fun mask => (mask,id))

def c39615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39615 : Upper (D 7) (R 7) [36,320,130,18,96] 13 := by
  apply FastRouting.sound _ _ [36,320,130,18,96] 13 (by decide) (choices 1) [1,8,128] r39615 c39615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27755
  · exact u27756
  · exact u27757

def r39616 : Route 9 := (fun mask => (mask,id))

def c39616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39616 : Upper (D 7) (R 7) [36,320,130,18,129] 13 := by
  apply FastRouting.sound _ _ [36,320,130,18,129] 13 (by decide) (choices 1) [1,8,64] r39616 c39616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27758
  · exact u27759
  · exact u27760

def b39617 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 37 322 134 26 152 97 97 225 353), lower := (rows 37 322 134 26 152 32 64 128 256), losses := [] }

theorem u39617 : Upper (D 7) (R 7) [36,320,130,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39618 : Route 9 := (fun mask => (mask,id))

def c39618 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39618 : Upper (D 7) (R 7) [36,320,130,18,160] 13 := by
  apply FastRouting.sound _ _ [36,320,130,18,160] 13 (by decide) (choices 1) [1,8,64] r39618 c39618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27761
  · exact u27762
  · exact u27763

def r39619 : Route 9 := (fun mask => (mask,id))

def c39619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39619 : Upper (D 7) (R 7) [36,320,130,18,192] 13 := by
  apply FastRouting.sound _ _ [36,320,130,18,192] 13 (by decide) (choices 1) [1,8] r39619 c39619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27764
  · exact u27765

def b39620 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 134 41 81 186 218 154 410), lower := (rows 37 322 134 41 81 32 64 128 256), losses := [] }

theorem u39620 : Upper (D 7) (R 7) [36,320,130,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39621 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 134 41 88 179 211 147 403), lower := (rows 37 322 134 41 88 32 64 128 256), losses := [] }

theorem u39621 : Upper (D 7) (R 7) [36,320,130,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39622 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 134 41 145 122 90 218 346), lower := (rows 37 322 134 41 145 32 64 128 256), losses := [] }

theorem u39622 : Upper (D 7) (R 7) [36,320,130,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39623 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 134 41 152 115 83 211 339), lower := (rows 37 322 134 41 152 32 64 128 256), losses := [] }

theorem u39623 : Upper (D 7) (R 7) [36,320,130,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39624 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 134 41 208 59 91 155 283), lower := (rows 37 322 134 41 208 32 64 128 256), losses := [] }

theorem u39624 : Upper (D 7) (R 7) [36,320,130,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39625 : Route 9 := (fun mask => (mask,id))

def c39625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39625 : Upper (D 7) (R 7) [36,320,130,34,65] 13 := by
  apply FastRouting.sound _ _ [36,320,130,34,65] 13 (by decide) (choices 1) [1,8,16,128] r39625 c39625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27766
  · exact u27767
  · exact u27768
  · exact u27769

def r39626 : Route 9 := (fun mask => (mask,id))

def c39626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39626 : Upper (D 7) (R 7) [36,320,130,34,72] 13 := by
  apply FastRouting.sound _ _ [36,320,130,34,72] 13 (by decide) (choices 1) [1,16,128] r39626 c39626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27770
  · exact u27771
  · exact u27772

def r39627 : Route 9 := (fun mask => (mask,id))

def c39627 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39627 : Upper (D 7) (R 7) [36,320,130,34,129] 13 := by
  apply FastRouting.sound _ _ [36,320,130,34,129] 13 (by decide) (choices 1) [1,8,16,64] r39627 c39627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27773
  · exact u27774
  · exact u27775
  · exact u27776

def r39628 : Route 9 := (fun mask => (mask,id))

def c39628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39628 : Upper (D 7) (R 7) [36,320,130,34,136] 13 := by
  apply FastRouting.sound _ _ [36,320,130,34,136] 13 (by decide) (choices 1) [1,16,64] r39628 c39628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27777
  · exact u27778
  · exact u27779

def r39629 : Route 9 := (fun mask => (mask,id))

def c39629 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39629 : Upper (D 7) (R 7) [36,320,130,34,192] 13 := by
  apply FastRouting.sound _ _ [36,320,130,34,192] 13 (by decide) (choices 1) [1,8,16] r39629 c39629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27780
  · exact u27781
  · exact u27782

def r39630 : Route 9 := (fun mask => (mask,id))

def c39630 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39630 : Upper (D 7) (R 7) [36,320,130,48,65] 13 := by
  apply FastRouting.sound _ _ [36,320,130,48,65] 13 (by decide) (choices 1) [1,2,8,128] r39630 c39630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27783
  · exact u27784
  · exact u27785
  · exact u27786

def b39631 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 134 56 82 169 201 137 393), lower := (rows 37 322 134 56 82 32 64 128 256), losses := [] }

theorem u39631 : Upper (D 7) (R 7) [36,320,130,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39632 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(2,6)], upper := (rows 37 322 134 56 88 163 195 131 387), lower := (rows 37 322 134 56 88 32 64 128 256), losses := [] }

theorem u39632 : Upper (D 7) (R 7) [36,320,130,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39633 : Route 9 := (fun mask => (mask,id))

def c39633 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39633 : Upper (D 7) (R 7) [36,320,130,48,129] 13 := by
  apply FastRouting.sound _ _ [36,320,130,48,129] 13 (by decide) (choices 1) [1,2,8,64] r39633 c39633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27787
  · exact u27788
  · exact u27789
  · exact u27790

def b39634 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 37 322 134 56 146 105 73 201 329), lower := (rows 37 322 134 56 146 32 64 128 256), losses := [] }

theorem u39634 : Upper (D 7) (R 7) [36,320,130,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39635 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,5)], upper := (rows 37 322 134 56 152 99 67 195 323), lower := (rows 37 322 134 56 152 32 64 128 256), losses := [] }

theorem u39635 : Upper (D 7) (R 7) [36,320,130,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39636 : Route 9 := (fun mask => (mask,id))

def c39636 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39636 : Upper (D 7) (R 7) [36,320,130,48,192] 13 := by
  apply FastRouting.sound _ _ [36,320,130,48,192] 13 (by decide) (choices 1) [1,2,8] r39636 c39636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27791
  · exact u27792
  · exact u27793

def r39637 : Route 9 := (fun mask => (mask,id))

def c39637 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39637 : Upper (D 7) (R 7) [36,320,130,65,129] 13 := by
  apply FastRouting.sound _ _ [36,320,130,65,129] 13 (by decide) (choices 1) [2,8,16] r39637 c39637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27794
  · exact u27795
  · exact u27796

def b39638 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 37 322 134 73 146 57 121 185 313), lower := (rows 37 322 134 73 146 32 64 128 256), losses := [] }

theorem u39638 : Upper (D 7) (R 7) [36,320,130,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39639 : Route 9 := (fun mask => (mask,id))

def c39639 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39639 : Upper (D 7) (R 7) [36,320,130,65,136] 13 := by
  apply FastRouting.sound _ _ [36,320,130,65,136] 13 (by decide) (choices 1) [1,2,16] r39639 c39639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27797
  · exact u27798
  · exact u27799

def r39640 : Route 9 := (fun mask => (mask,id))

def c39640 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39640 : Upper (D 7) (R 7) [36,320,130,65,160] 13 := by
  apply FastRouting.sound _ _ [36,320,130,65,160] 13 (by decide) (choices 1) [1,2,8,16] r39640 c39640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27800
  · exact u27801
  · exact u27802
  · exact u27803

def b39641 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 134 74 145 57 121 185 313), lower := (rows 37 322 134 74 145 32 64 128 256), losses := [] }

theorem u39641 : Upper (D 7) (R 7) [36,320,130,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39642 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 134 74 152 49 113 177 305), lower := (rows 37 322 134 74 152 32 64 128 256), losses := [] }

theorem u39642 : Upper (D 7) (R 7) [36,320,130,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39643 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 134 74 176 57 89 153 281), lower := (rows 37 322 134 74 176 32 64 128 256), losses := [] }

theorem u39643 : Upper (D 7) (R 7) [36,320,130,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39644 : Route 9 := (fun mask => (mask,id))

def c39644 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39644 : Upper (D 7) (R 7) [36,320,130,80,129] 13 := by
  apply FastRouting.sound _ _ [36,320,130,80,129] 13 (by decide) (choices 1) [1,2,8] r39644 c39644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27804
  · exact u27805
  · exact u27806

def b39645 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 37 322 134 88 146 41 105 169 297), lower := (rows 37 322 134 88 146 32 64 128 256), losses := [] }

theorem u39645 : Upper (D 7) (R 7) [36,320,130,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39646 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(2,6)], upper := (rows 37 322 134 88 152 35 99 163 291), lower := (rows 37 322 134 88 152 32 64 128 256), losses := [] }

theorem u39646 : Upper (D 7) (R 7) [36,320,130,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39647 : Route 9 := (fun mask => (mask,id))

def c39647 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39647 : Upper (D 7) (R 7) [36,320,130,80,160] 13 := by
  apply FastRouting.sound _ _ [36,320,130,80,160] 13 (by decide) (choices 1) [1,2,8] r39647 c39647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27807
  · exact u27808
  · exact u27809

def r39648 : Route 9 := (fun mask => (mask,id))

def c39648 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39648 : Upper (D 7) (R 7) [36,320,130,96,129] 13 := by
  apply FastRouting.sound _ _ [36,320,130,96,129] 13 (by decide) (choices 1) [1,2,8,16] r39648 c39648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27810
  · exact u27811
  · exact u27812
  · exact u27813

def b39649 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 37 322 134 104 146 57 89 153 281), lower := (rows 37 322 134 104 146 32 64 128 256), losses := [] }

theorem u39649 : Upper (D 7) (R 7) [36,320,130,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39650 : Route 9 := (fun mask => (mask,id))

def c39650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39650 : Upper (D 7) (R 7) [36,320,130,96,136] 13 := by
  apply FastRouting.sound _ _ [36,320,130,96,136] 13 (by decide) (choices 1) [1,2,16] r39650 c39650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27814
  · exact u27815
  · exact u27816

def b39651 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 37 322 140 11 19 240 240 240 496), lower := (rows 37 322 140 11 19 32 64 128 256), losses := [] }

theorem u39651 : Upper (D 7) (R 7) [36,320,136,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39652 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 140 11 49 242 210 210 466), lower := (rows 37 322 140 11 49 32 64 128 256), losses := [] }

theorem u39652 : Upper (D 7) (R 7) [36,320,136,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39653 : Route 9 := (fun mask => (mask,id))

def c39653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39653 : Upper (D 7) (R 7) [36,320,136,3,34] 13 := by
  apply FastRouting.sound _ _ [36,320,136,3,34] 13 (by decide) (choices 1) [1,16,64,128] r39653 c39653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27817
  · exact u27818
  · exact u27819
  · exact u27820

def r39654 : Route 9 := (fun mask => (mask,id))

def c39654 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39654 : Upper (D 7) (R 7) [36,320,136,3,65] 13 := by
  apply FastRouting.sound _ _ [36,320,136,3,65] 13 (by decide) (choices 1) [2,16,128] r39654 c39654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27821
  · exact u27822
  · exact u27823

def b39655 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 140 11 82 177 241 177 433), lower := (rows 37 322 140 11 82 32 64 128 256), losses := [] }

theorem u39655 : Upper (D 7) (R 7) [36,320,136,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39656 : Route 9 := (fun mask => (mask,id))

def c39656 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39656 : Upper (D 7) (R 7) [36,320,136,3,96] 13 := by
  apply FastRouting.sound _ _ [36,320,136,3,96] 13 (by decide) (choices 1) [1,2,16,128] r39656 c39656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27824
  · exact u27825
  · exact u27826
  · exact u27827

def r39657 : Route 9 := (fun mask => (mask,id))

def c39657 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39657 : Upper (D 7) (R 7) [36,320,136,3,129] 13 := by
  apply FastRouting.sound _ _ [36,320,136,3,129] 13 (by decide) (choices 1) [2,16,64] r39657 c39657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27828
  · exact u27829
  · exact u27830

def r39658 : Route 9 := (fun mask => (mask,id))

def c39658 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39658 : Upper (D 7) (R 7) [36,320,136,3,130] 13 := by
  apply FastRouting.sound _ _ [36,320,136,3,130] 13 (by decide) (choices 1) [1,16,64] r39658 c39658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27831
  · exact u27832
  · exact u27833

def r39659 : Route 9 := (fun mask => (mask,id))

def c39659 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39659 : Upper (D 7) (R 7) [36,320,136,3,160] 13 := by
  apply FastRouting.sound _ _ [36,320,136,3,160] 13 (by decide) (choices 1) [1,2,16,64] r39659 c39659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27834
  · exact u27835
  · exact u27836
  · exact u27837

#print axioms u39659
end Delivery.IrregularNine14.P07
