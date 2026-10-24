import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0210
import IrregularNine14P07C0211
import IrregularNine14P07C0212

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30600 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 16, targets := 64 }], pairs := [(0,5),(2,5),(3,5),(4,6)], upper := (rows 7 35 268 73 50 240 208 208 464), lower := (rows 7 35 268 73 50 32 64 128 256), losses := [] }

theorem u30600 : Upper (D 7) (R 7) [6,33,264,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30601 : Route 9 := (fun mask => (mask,id))

def c30601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30601 : Upper (D 7) (R 7) [6,33,264,65,66] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,66] 13 (by decide) (choices 1) [16,128] r30601 c30601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12620
  · exact u12621

def r30602 : Route 9 := (fun mask => (mask,id))

def c30602 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30602 : Upper (D 7) (R 7) [6,33,264,65,96] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,96] 13 (by decide) (choices 1) [2,16,128] r30602 c30602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12622
  · exact u12623
  · exact u12624

def r30603 : Route 9 := (fun mask => (mask,id))

def c30603 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30603 : Upper (D 7) (R 7) [6,33,264,65,130] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,130] 13 (by decide) (choices 1) [16,64,128] r30603 c30603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12625
  · exact u12626
  · exact u12627

def r30604 : Route 9 := (fun mask => (mask,id))

def c30604 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30604 : Upper (D 7) (R 7) [6,33,264,65,160] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,160] 13 (by decide) (choices 1) [2,16,64,128] r30604 c30604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12628
  · exact u12629
  · exact u12630
  · exact u12631

def r30605 : Route 9 := (fun mask => (mask,id))

def c30605 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30605 : Upper (D 7) (R 7) [6,33,264,65,192] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,192] 13 (by decide) (choices 1) [2,16,128] r30605 c30605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12632
  · exact u12633
  · exact u12634

def b30606 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 7 35 268 74 49 240 208 208 464), lower := (rows 7 35 268 74 49 32 64 128 256), losses := [] }

theorem u30606 : Upper (D 7) (R 7) [6,33,264,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30607 : Route 9 := (fun mask => (mask,id))

def c30607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30607 : Upper (D 7) (R 7) [6,33,264,66,65] 13 := by
  apply FastRouting.sound _ _ [6,33,264,66,65] 13 (by decide) (choices 1) [16,128] r30607 c30607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12635
  · exact u12636

def r30608 : Route 9 := (fun mask => (mask,id))

def c30608 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30608 : Upper (D 7) (R 7) [6,33,264,66,96] 13 := by
  apply FastRouting.sound _ _ [6,33,264,66,96] 13 (by decide) (choices 1) [1,16,128] r30608 c30608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12637
  · exact u12638
  · exact u12639

def r30609 : Route 9 := (fun mask => (mask,id))

def c30609 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30609 : Upper (D 7) (R 7) [6,33,264,66,129] 13 := by
  apply FastRouting.sound _ _ [6,33,264,66,129] 13 (by decide) (choices 1) [16,64,128] r30609 c30609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12640
  · exact u12641
  · exact u12642

def r30610 : Route 9 := (fun mask => (mask,id))

def c30610 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30610 : Upper (D 7) (R 7) [6,33,264,66,160] 13 := by
  apply FastRouting.sound _ _ [6,33,264,66,160] 13 (by decide) (choices 1) [1,16,64,128] r30610 c30610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12643
  · exact u12644
  · exact u12645
  · exact u12646

def r30611 : Route 9 := (fun mask => (mask,id))

def c30611 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30611 : Upper (D 7) (R 7) [6,33,264,66,192] 13 := by
  apply FastRouting.sound _ _ [6,33,264,66,192] 13 (by decide) (choices 1) [1,16,128] r30611 c30611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12647
  · exact u12648
  · exact u12649

def b30612 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 268 88 19 224 224 224 480), lower := (rows 7 35 268 88 19 32 64 128 256), losses := [] }

theorem u30612 : Upper (D 7) (R 7) [6,33,264,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30613 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 7 35 268 88 49 226 194 194 450), lower := (rows 7 35 268 88 49 32 64 128 256), losses := [] }

theorem u30613 : Upper (D 7) (R 7) [6,33,264,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30614 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 35 268 88 50 225 193 193 449), lower := (rows 7 35 268 88 50 32 64 128 256), losses := [] }

theorem u30614 : Upper (D 7) (R 7) [6,33,264,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30615 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 35 268 88 81 162 226 162 418), lower := (rows 7 35 268 88 81 32 64 128 256), losses := [] }

theorem u30615 : Upper (D 7) (R 7) [6,33,264,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30616 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 35 268 88 82 161 225 161 417), lower := (rows 7 35 268 88 82 32 64 128 256), losses := [] }

theorem u30616 : Upper (D 7) (R 7) [6,33,264,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30617 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 35 268 88 112 163 195 131 387), lower := (rows 7 35 268 88 112 32 64 128 256), losses := [] }

theorem u30617 : Upper (D 7) (R 7) [6,33,264,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30618 : Route 9 := (fun mask => (mask,id))

def c30618 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30618 : Upper (D 7) (R 7) [6,33,264,80,129] 13 := by
  apply FastRouting.sound _ _ [6,33,264,80,129] 13 (by decide) (choices 1) [2,64,128] r30618 c30618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12650
  · exact u12651
  · exact u12652

def r30619 : Route 9 := (fun mask => (mask,id))

def c30619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30619 : Upper (D 7) (R 7) [6,33,264,80,130] 13 := by
  apply FastRouting.sound _ _ [6,33,264,80,130] 13 (by decide) (choices 1) [1,64,128] r30619 c30619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12653
  · exact u12654
  · exact u12655

def r30620 : Route 9 := (fun mask => (mask,id))

def c30620 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30620 : Upper (D 7) (R 7) [6,33,264,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,264,80,160] 13 (by decide) (choices 1) [1,2,64,128] r30620 c30620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12656
  · exact u12657
  · exact u12658
  · exact u12659

def b30621 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 35 268 88 208 163 227 163 419), lower := (rows 7 35 268 88 208 32 64 128 256), losses := [] }

theorem u30621 : Upper (D 7) (R 7) [6,33,264,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30622 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 268 104 19 240 208 208 464), lower := (rows 7 35 268 104 19 32 64 128 256), losses := [] }

theorem u30622 : Upper (D 7) (R 7) [6,33,264,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30623 : Route 9 := (fun mask => (mask,id))

def c30623 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30623 : Upper (D 7) (R 7) [6,33,264,96,65] 13 := by
  apply FastRouting.sound _ _ [6,33,264,96,65] 13 (by decide) (choices 1) [2,16,128] r30623 c30623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12660
  · exact u12661
  · exact u12662

def r30624 : Route 9 := (fun mask => (mask,id))

def c30624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30624 : Upper (D 7) (R 7) [6,33,264,96,66] 13 := by
  apply FastRouting.sound _ _ [6,33,264,96,66] 13 (by decide) (choices 1) [1,16,128] r30624 c30624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12663
  · exact u12664
  · exact u12665

def r30625 : Route 9 := (fun mask => (mask,id))

def c30625 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30625 : Upper (D 7) (R 7) [6,33,264,96,129] 13 := by
  apply FastRouting.sound _ _ [6,33,264,96,129] 13 (by decide) (choices 1) [2,16,64,128] r30625 c30625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12666
  · exact u12667
  · exact u12668
  · exact u12669

def r30626 : Route 9 := (fun mask => (mask,id))

def c30626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30626 : Upper (D 7) (R 7) [6,33,264,96,130] 13 := by
  apply FastRouting.sound _ _ [6,33,264,96,130] 13 (by decide) (choices 1) [1,16,64,128] r30626 c30626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12670
  · exact u12671
  · exact u12672
  · exact u12673

def r30627 : Route 9 := (fun mask => (mask,id))

def c30627 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30627 : Upper (D 7) (R 7) [6,33,264,96,192] 13 := by
  apply FastRouting.sound _ _ [6,33,264,96,192] 13 (by decide) (choices 1) [1,2,16,128] r30627 c30627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12674
  · exact u12675
  · exact u12676
  · exact u12677

def b30628 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 268 200 19 240 240 240 496), lower := (rows 7 35 268 200 19 32 64 128 256), losses := [] }

theorem u30628 : Upper (D 7) (R 7) [6,33,264,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30629 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 7 35 268 200 49 242 210 210 466), lower := (rows 7 35 268 200 49 32 64 128 256), losses := [] }

theorem u30629 : Upper (D 7) (R 7) [6,33,264,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30630 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 35 268 200 50 241 209 209 465), lower := (rows 7 35 268 200 50 32 64 128 256), losses := [] }

theorem u30630 : Upper (D 7) (R 7) [6,33,264,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30631 : Route 9 := (fun mask => (mask,id))

def c30631 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30631 : Upper (D 7) (R 7) [6,33,264,192,65] 13 := by
  apply FastRouting.sound _ _ [6,33,264,192,65] 13 (by decide) (choices 1) [2,16,128] r30631 c30631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12678
  · exact u12679
  · exact u12680

def r30632 : Route 9 := (fun mask => (mask,id))

def c30632 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30632 : Upper (D 7) (R 7) [6,33,264,192,66] 13 := by
  apply FastRouting.sound _ _ [6,33,264,192,66] 13 (by decide) (choices 1) [1,16,128] r30632 c30632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12681
  · exact u12682
  · exact u12683

def r30633 : Route 9 := (fun mask => (mask,id))

def c30633 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30633 : Upper (D 7) (R 7) [6,33,264,192,96] 13 := by
  apply FastRouting.sound _ _ [6,33,264,192,96] 13 (by decide) (choices 1) [1,2,16,128] r30633 c30633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12684
  · exact u12685
  · exact u12686
  · exact u12687

def b30634 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 35 268 200 208 51 115 179 307), lower := (rows 7 35 268 200 208 32 64 128 256), losses := [] }

theorem u30634 : Upper (D 7) (R 7) [6,33,264,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30635 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 324 11 56 240 208 208 464), lower := (rows 7 35 324 11 56 32 64 128 256), losses := [] }

theorem u30635 : Upper (D 7) (R 7) [6,33,320,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30636 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 324 11 88 176 240 176 432), lower := (rows 7 35 324 11 88 32 64 128 256), losses := [] }

theorem u30636 : Upper (D 7) (R 7) [6,33,320,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30637 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 324 11 112 184 216 152 408), lower := (rows 7 35 324 11 112 32 64 128 256), losses := [] }

theorem u30637 : Upper (D 7) (R 7) [6,33,320,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30638 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 324 11 152 240 240 240 496), lower := (rows 7 35 324 11 152 32 64 128 256), losses := [] }

theorem u30638 : Upper (D 7) (R 7) [6,33,320,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30639 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 324 11 176 248 216 216 472), lower := (rows 7 35 324 11 176 32 64 128 256), losses := [] }

theorem u30639 : Upper (D 7) (R 7) [6,33,320,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30640 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 324 11 208 184 248 184 440), lower := (rows 7 35 324 11 208 32 64 128 256), losses := [] }

theorem u30640 : Upper (D 7) (R 7) [6,33,320,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30641 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 35 324 25 26 224 224 224 480), lower := (rows 7 35 324 25 26 32 64 128 256), losses := [] }

theorem u30641 : Upper (D 7) (R 7) [6,33,320,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30642 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 324 25 50 232 200 200 456), lower := (rows 7 35 324 25 50 32 64 128 256), losses := [] }

theorem u30642 : Upper (D 7) (R 7) [6,33,320,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30643 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 324 25 56 226 194 194 450), lower := (rows 7 35 324 25 56 32 64 128 256), losses := [] }

theorem u30643 : Upper (D 7) (R 7) [6,33,320,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30644 : Route 9 := (fun mask => (mask,id))

def c30644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30644 : Upper (D 7) (R 7) [6,33,320,17,66] 13 := by
  apply FastRouting.sound _ _ [6,33,320,17,66] 13 (by decide) (choices 1) [8,128] r30644 c30644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12688
  · exact u12689

def b30645 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 0, region := 484, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 7 35 324 25 88 162 226 162 418), lower := (rows 7 35 324 25 88 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 15 8 24 35 67 131 259), good := (rows 486 486 324 508 92 32 64 128 256) }] }

theorem u30645 : Upper (D 7) (R 7) [6,33,320,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30646 : Route 9 := (fun mask => (mask,id))

def c30646 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30646 : Upper (D 7) (R 7) [6,33,320,17,96] 13 := by
  apply FastRouting.sound _ _ [6,33,320,17,96] 13 (by decide) (choices 1) [2,8,128] r30646 c30646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12690
  · exact u12691
  · exact u12692

def r30647 : Route 9 := (fun mask => (mask,id))

def c30647 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30647 : Upper (D 7) (R 7) [6,33,320,17,130] 13 := by
  apply FastRouting.sound _ _ [6,33,320,17,130] 13 (by decide) (choices 1) [8,64,128] r30647 c30647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12693
  · exact u12694
  · exact u12695

def r30648 : Route 9 := (fun mask => (mask,id))

def c30648 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30648 : Upper (D 7) (R 7) [6,33,320,17,136] 13 := by
  apply FastRouting.sound _ _ [6,33,320,17,136] 13 (by decide) (choices 1) [2,64,128] r30648 c30648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12696
  · exact u12697
  · exact u12698

def r30649 : Route 9 := (fun mask => (mask,id))

def c30649 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30649 : Upper (D 7) (R 7) [6,33,320,17,160] 13 := by
  apply FastRouting.sound _ _ [6,33,320,17,160] 13 (by decide) (choices 1) [2,8,64,128] r30649 c30649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12699
  · exact u12700
  · exact u12701
  · exact u12702

def r30650 : Route 9 := (fun mask => (mask,id))

def c30650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30650 : Upper (D 7) (R 7) [6,33,320,17,192] 13 := by
  apply FastRouting.sound _ _ [6,33,320,17,192] 13 (by decide) (choices 1) [2,8,128] r30650 c30650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12703
  · exact u12704
  · exact u12705

def b30651 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 324 26 49 232 200 200 456), lower := (rows 7 35 324 26 49 32 64 128 256), losses := [] }

theorem u30651 : Upper (D 7) (R 7) [6,33,320,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30652 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 7 35 324 26 56 225 193 193 449), lower := (rows 7 35 324 26 56 32 64 128 256), losses := [] }

theorem u30652 : Upper (D 7) (R 7) [6,33,320,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30653 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6),(2,0),(2,1),(3,6)], upper := (rows 7 35 324 26 81 168 232 168 424), lower := (rows 7 35 324 26 81 32 64 128 256), losses := [] }

theorem u30653 : Upper (D 7) (R 7) [6,33,320,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30654 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(4,1)], upper := (rows 7 35 324 26 88 161 225 161 417), lower := (rows 7 35 324 26 88 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 15 8 24 35 67 131 259), good := (rows 485 485 324 508 92 32 64 128 256) }] }

theorem u30654 : Upper (D 7) (R 7) [6,33,320,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30655 : Route 9 := (fun mask => (mask,id))

def c30655 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30655 : Upper (D 7) (R 7) [6,33,320,18,96] 13 := by
  apply FastRouting.sound _ _ [6,33,320,18,96] 13 (by decide) (choices 1) [1,8,128] r30655 c30655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12706
  · exact u12707
  · exact u12708

def r30656 : Route 9 := (fun mask => (mask,id))

def c30656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30656 : Upper (D 7) (R 7) [6,33,320,18,129] 13 := by
  apply FastRouting.sound _ _ [6,33,320,18,129] 13 (by decide) (choices 1) [8,64,128] r30656 c30656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12709
  · exact u12710
  · exact u12711

def r30657 : Route 9 := (fun mask => (mask,id))

def c30657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30657 : Upper (D 7) (R 7) [6,33,320,18,136] 13 := by
  apply FastRouting.sound _ _ [6,33,320,18,136] 13 (by decide) (choices 1) [1,64,128] r30657 c30657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12712
  · exact u12713
  · exact u12714

def r30658 : Route 9 := (fun mask => (mask,id))

def c30658 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30658 : Upper (D 7) (R 7) [6,33,320,18,160] 13 := by
  apply FastRouting.sound _ _ [6,33,320,18,160] 13 (by decide) (choices 1) [1,8,64,128] r30658 c30658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12715
  · exact u12716
  · exact u12717
  · exact u12718

def r30659 : Route 9 := (fun mask => (mask,id))

def c30659 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30659 : Upper (D 7) (R 7) [6,33,320,18,192] 13 := by
  apply FastRouting.sound _ _ [6,33,320,18,192] 13 (by decide) (choices 1) [1,8,128] r30659 c30659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12719
  · exact u12720
  · exact u12721

#print axioms u30659
end Delivery.IrregularNine14.P07
