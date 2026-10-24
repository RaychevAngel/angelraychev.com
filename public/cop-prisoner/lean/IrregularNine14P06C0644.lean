import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0410
import IrregularNine14P06C0411

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38640 : Route 9 := (fun mask => (mask,id))

def c38640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38640 : Upper (D 6) (R 6) [34,192,40,258,5] 13 := by
  apply FastRouting.sound _ _ [34,192,40,258,5] 13 (by decide) (choices 1) [1,4,16,64] r38640 c38640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24616
  · exact u24617
  · exact u24618
  · exact u24619

def r38641 : Route 9 := (fun mask => (mask,id))

def c38641 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38641 : Upper (D 6) (R 6) [34,192,40,258,65] 13 := by
  apply FastRouting.sound _ _ [34,192,40,258,65] 13 (by decide) (choices 1) [1,4,16] r38641 c38641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24620
  · exact u24621
  · exact u24622

def r38642 : Route 9 := (fun mask => (mask,id))

def c38642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38642 : Upper (D 6) (R 6) [34,192,40,258,68] 13 := by
  apply FastRouting.sound _ _ [34,192,40,258,68] 13 (by decide) (choices 1) [1,4,16] r38642 c38642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24623
  · exact u24624
  · exact u24625

def b38643 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 44 268 19 117 85 213 341), lower := (rows 35 194 44 268 19 32 64 128 256), losses := [] }

theorem u38643 : Upper (D 6) (R 6) [34,192,40,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38644 : PairBound 9 := { available := 83, camps := [{ cop := 4, region := 227, targets := 4 },{ cop := 4, region := 194, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 194 44 268 21 115 83 211 339), lower := (rows 35 194 44 268 21 32 64 128 256), losses := [] }

theorem u38644 : Upper (D 6) (R 6) [34,192,40,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38645 : Route 9 := (fun mask => (mask,id))

def c38645 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38645 : Upper (D 6) (R 6) [34,192,40,260,6] 13 := by
  apply FastRouting.sound _ _ [34,192,40,260,6] 13 (by decide) (choices 1) [1,16,64] r38645 c38645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24626
  · exact u24627
  · exact u24628

def r38646 : Route 9 := (fun mask => (mask,id))

def c38646 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38646 : Upper (D 6) (R 6) [34,192,40,260,65] 13 := by
  apply FastRouting.sound _ _ [34,192,40,260,65] 13 (by decide) (choices 1) [1,2,4,16] r38646 c38646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24629
  · exact u24630
  · exact u24631
  · exact u24632

def b38647 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 44 268 82 53 85 149 277), lower := (rows 35 194 44 268 82 32 64 128 256), losses := [] }

theorem u38647 : Upper (D 6) (R 6) [34,192,40,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38648 : Route 9 := (fun mask => (mask,id))

def c38648 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38648 : Upper (D 6) (R 6) [34,192,40,260,68] 13 := by
  apply FastRouting.sound _ _ [34,192,40,260,68] 13 (by decide) (choices 1) [1,2,16] r38648 c38648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24633
  · exact u24634
  · exact u24635

def b38649 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 44 280 19 101 69 197 325), lower := (rows 35 194 44 280 19 32 64 128 256), losses := [] }

theorem u38649 : Upper (D 6) (R 6) [34,192,40,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38650 : Route 9 := (fun mask => (mask,id))

def c38650 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38650 : Upper (D 6) (R 6) [34,192,40,272,5] 13 := by
  apply FastRouting.sound _ _ [34,192,40,272,5] 13 (by decide) (choices 1) [1,2,4,64] r38650 c38650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24636
  · exact u24637
  · exact u24638
  · exact u24639

def r38651 : Route 9 := (fun mask => (mask,id))

def c38651 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38651 : Upper (D 6) (R 6) [34,192,40,272,6] 13 := by
  apply FastRouting.sound _ _ [34,192,40,272,6] 13 (by decide) (choices 1) [1,4,64] r38651 c38651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24640
  · exact u24641
  · exact u24642

def r38652 : Route 9 := (fun mask => (mask,id))

def c38652 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38652 : Upper (D 6) (R 6) [34,192,40,272,65] 13 := by
  apply FastRouting.sound _ _ [34,192,40,272,65] 13 (by decide) (choices 1) [1,2,4] r38652 c38652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24643
  · exact u24644
  · exact u24645

def b38653 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 44 280 82 37 69 133 261), lower := (rows 35 194 44 280 82 32 64 128 256), losses := [] }

theorem u38653 : Upper (D 6) (R 6) [34,192,40,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38654 : Route 9 := (fun mask => (mask,id))

def c38654 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38654 : Upper (D 6) (R 6) [34,192,40,272,68] 13 := by
  apply FastRouting.sound _ _ [34,192,40,272,68] 13 (by decide) (choices 1) [1,2,4] r38654 c38654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24646
  · exact u24647
  · exact u24648

def b38655 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 44 328 19 53 85 149 277), lower := (rows 35 194 44 328 19 32 64 128 256), losses := [] }

theorem u38655 : Upper (D 6) (R 6) [34,192,40,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38656 : Route 9 := (fun mask => (mask,id))

def c38656 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38656 : Upper (D 6) (R 6) [34,192,40,320,5] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,5] 13 (by decide) (choices 1) [1,2,4,16] r38656 c38656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24649
  · exact u24650
  · exact u24651
  · exact u24652

def r38657 : Route 9 := (fun mask => (mask,id))

def c38657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38657 : Upper (D 6) (R 6) [34,192,40,320,6] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,6] 13 (by decide) (choices 1) [1,4,16] r38657 c38657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24653
  · exact u24654
  · exact u24655

def b38658 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 76 13 19 308 372 436 308), lower := (rows 35 194 76 13 19 32 64 128 256), losses := [] }

theorem u38658 : Upper (D 6) (R 6) [34,192,72,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38659 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 194 76 13 21 306 370 434 306), lower := (rows 35 194 76 13 21 32 64 128 256), losses := [] }

theorem u38659 : Upper (D 6) (R 6) [34,192,72,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38660 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 483, targets := 4 },{ cop := 4, region := 289, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 76 13 22 305 369 433 305), lower := (rows 35 194 76 13 22 32 64 128 256), losses := [] }

theorem u38660 : Upper (D 6) (R 6) [34,192,72,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38661 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 76 13 49 310 342 406 278), lower := (rows 35 194 76 13 49 32 64 128 256), losses := [] }

theorem u38661 : Upper (D 6) (R 6) [34,192,72,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38662 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 194 76 13 50 309 341 405 277), lower := (rows 35 194 76 13 50 32 64 128 256), losses := [] }

theorem u38662 : Upper (D 6) (R 6) [34,192,72,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38663 : Route 9 := (fun mask => (mask,id))

def c38663 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38663 : Upper (D 6) (R 6) [34,192,72,5,36] 13 := by
  apply FastRouting.sound _ _ [34,192,72,5,36] 13 (by decide) (choices 1) [1,2,16,256] r38663 c38663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24656
  · exact u24657
  · exact u24658
  · exact u24659

def r38664 : Route 9 := (fun mask => (mask,id))

def c38664 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38664 : Upper (D 6) (R 6) [34,192,72,5,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,5,257] 13 (by decide) (choices 1) [2,4,16] r38664 c38664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24660
  · exact u24661
  · exact u24662

def r38665 : Route 9 := (fun mask => (mask,id))

def c38665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38665 : Upper (D 6) (R 6) [34,192,72,5,258] 13 := by
  apply FastRouting.sound _ _ [34,192,72,5,258] 13 (by decide) (choices 1) [1,4,16] r38665 c38665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24663
  · exact u24664
  · exact u24665

def r38666 : Route 9 := (fun mask => (mask,id))

def c38666 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38666 : Upper (D 6) (R 6) [34,192,72,5,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,5,260] 13 (by decide) (choices 1) [1,2,16] r38666 c38666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24666
  · exact u24667
  · exact u24668

def r38667 : Route 9 := (fun mask => (mask,id))

def c38667 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38667 : Upper (D 6) (R 6) [34,192,72,5,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,5,288] 13 (by decide) (choices 1) [1,2,4,16] r38667 c38667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24669
  · exact u24670
  · exact u24671
  · exact u24672

def b38668 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 76 25 19 292 356 420 292), lower := (rows 35 194 76 25 19 32 64 128 256), losses := [] }

theorem u38668 : Upper (D 6) (R 6) [34,192,72,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38669 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 76 25 21 294 358 422 294), lower := (rows 35 194 76 25 21 32 64 128 256), losses := [] }

theorem u38669 : Upper (D 6) (R 6) [34,192,72,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38670 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 297, targets := 64 },{ cop := 3, region := 356, targets := 2 }], pairs := [(0,6),(2,1),(3,6)], upper := (rows 35 194 76 25 22 293 357 421 293), lower := (rows 35 194 76 25 22 32 64 128 256), losses := [] }

theorem u38670 : Upper (D 6) (R 6) [34,192,72,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38671 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 76 25 49 294 326 390 262), lower := (rows 35 194 76 25 49 32 64 128 256), losses := [] }

theorem u38671 : Upper (D 6) (R 6) [34,192,72,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38672 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 76 25 50 293 325 389 261), lower := (rows 35 194 76 25 50 32 64 128 256), losses := [] }

theorem u38672 : Upper (D 6) (R 6) [34,192,72,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38673 : Route 9 := (fun mask => (mask,id))

def c38673 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38673 : Upper (D 6) (R 6) [34,192,72,17,36] 13 := by
  apply FastRouting.sound _ _ [34,192,72,17,36] 13 (by decide) (choices 1) [1,2,4,256] r38673 c38673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24673
  · exact u24674
  · exact u24675
  · exact u24676

def b38674 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 76 25 273 38 102 166 294), lower := (rows 35 194 76 25 273 32 64 128 256), losses := [] }

theorem u38674 : Upper (D 6) (R 6) [34,192,72,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38675 : Route 9 := (fun mask => (mask,id))

def c38675 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38675 : Upper (D 6) (R 6) [34,192,72,17,258] 13 := by
  apply FastRouting.sound _ _ [34,192,72,17,258] 13 (by decide) (choices 1) [1,4] r38675 c38675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24677
  · exact u24678

def r38676 : Route 9 := (fun mask => (mask,id))

def c38676 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38676 : Upper (D 6) (R 6) [34,192,72,17,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,17,260] 13 (by decide) (choices 1) [1,2,4] r38676 c38676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24679
  · exact u24680
  · exact u24681

def r38677 : Route 9 := (fun mask => (mask,id))

def c38677 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38677 : Upper (D 6) (R 6) [34,192,72,17,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,17,288] 13 (by decide) (choices 1) [1,2,4] r38677 c38677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24682
  · exact u24683
  · exact u24684

def b38678 : PairBound 9 := { available := 293, camps := [], pairs := [(0,6),(2,1),(4,6)], upper := (rows 35 194 76 26 21 293 357 421 293), lower := (rows 35 194 76 26 21 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 48 80 144 272), good := (rows 33 192 76 508 501 32 64 128 256) },{ target := 6, region := (rows 9 2 4 8 20 52 0 148 276), good := (rows 35 130 445 443 437 32 0 128 256) }] }

theorem u38678 : Upper (D 6) (R 6) [34,192,72,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38679 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 76 26 49 293 325 389 261), lower := (rows 35 194 76 26 49 32 64 128 256), losses := [] }

theorem u38679 : Upper (D 6) (R 6) [34,192,72,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38680 : Route 9 := (fun mask => (mask,id))

def c38680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38680 : Upper (D 6) (R 6) [34,192,72,18,36] 13 := by
  apply FastRouting.sound _ _ [34,192,72,18,36] 13 (by decide) (choices 1) [1,4,256] r38680 c38680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24685
  · exact u24686
  · exact u24687

def r38681 : Route 9 := (fun mask => (mask,id))

def c38681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38681 : Upper (D 6) (R 6) [34,192,72,18,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,18,257] 13 (by decide) (choices 1) [1,4] r38681 c38681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24688
  · exact u24689

def r38682 : Route 9 := (fun mask => (mask,id))

def c38682 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38682 : Upper (D 6) (R 6) [34,192,72,18,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,18,260] 13 (by decide) (choices 1) [1,4] r38682 c38682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24690
  · exact u24691

def r38683 : Route 9 := (fun mask => (mask,id))

def c38683 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38683 : Upper (D 6) (R 6) [34,192,72,18,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,18,288] 13 (by decide) (choices 1) [1,4] r38683 c38683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24692
  · exact u24693

def b38684 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 76 28 19 293 357 421 293), lower := (rows 35 194 76 28 19 32 64 128 256), losses := [] }

theorem u38684 : Upper (D 6) (R 6) [34,192,72,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38685 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 76 28 21 291 355 419 291), lower := (rows 35 194 76 28 21 32 64 128 256), losses := [] }

theorem u38685 : Upper (D 6) (R 6) [34,192,72,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38686 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 28, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 35 194 76 28 22 289 353 417 289), lower := (rows 35 194 76 28 22 32 64 128 256), losses := [] }

theorem u38686 : Upper (D 6) (R 6) [34,192,72,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38687 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 76 28 49 295 327 391 263), lower := (rows 35 194 76 28 49 32 64 128 256), losses := [] }

theorem u38687 : Upper (D 6) (R 6) [34,192,72,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38688 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 194 76 28 50 293 325 389 261), lower := (rows 35 194 76 28 50 32 64 128 256), losses := [] }

theorem u38688 : Upper (D 6) (R 6) [34,192,72,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38689 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 76 28 52 291 323 387 259), lower := (rows 35 194 76 28 52 32 64 128 256), losses := [] }

theorem u38689 : Upper (D 6) (R 6) [34,192,72,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38690 : Route 9 := (fun mask => (mask,id))

def c38690 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38690 : Upper (D 6) (R 6) [34,192,72,20,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,20,257] 13 (by decide) (choices 1) [1,2,4] r38690 c38690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24694
  · exact u24695
  · exact u24696

def r38691 : Route 9 := (fun mask => (mask,id))

def c38691 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38691 : Upper (D 6) (R 6) [34,192,72,20,258] 13 := by
  apply FastRouting.sound _ _ [34,192,72,20,258] 13 (by decide) (choices 1) [1,4] r38691 c38691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24697
  · exact u24698

def b38692 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 76 28 276 35 99 163 291), lower := (rows 35 194 76 28 276 32 64 128 256), losses := [] }

theorem u38692 : Upper (D 6) (R 6) [34,192,72,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38693 : Route 9 := (fun mask => (mask,id))

def c38693 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38693 : Upper (D 6) (R 6) [34,192,72,20,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,20,288] 13 (by decide) (choices 1) [1,2,4] r38693 c38693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24699
  · exact u24700
  · exact u24701

def b38694 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 76 44 19 309 341 405 277), lower := (rows 35 194 76 44 19 32 64 128 256), losses := [] }

theorem u38694 : Upper (D 6) (R 6) [34,192,72,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38695 : PairBound 9 := { available := 275, camps := [{ cop := 4, region := 483, targets := 4 },{ cop := 4, region := 450, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 194 76 44 21 307 339 403 275), lower := (rows 35 194 76 44 21 32 64 128 256), losses := [] }

theorem u38695 : Upper (D 6) (R 6) [34,192,72,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38696 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 483, targets := 4 },{ cop := 4, region := 289, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 76 44 22 305 337 401 273), lower := (rows 35 194 76 44 22 32 64 128 256), losses := [] }

theorem u38696 : Upper (D 6) (R 6) [34,192,72,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38697 : Route 9 := (fun mask => (mask,id))

def c38697 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38697 : Upper (D 6) (R 6) [34,192,72,36,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,36,257] 13 (by decide) (choices 1) [1,2,4,16] r38697 c38697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24702
  · exact u24703
  · exact u24704
  · exact u24705

def r38698 : Route 9 := (fun mask => (mask,id))

def c38698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38698 : Upper (D 6) (R 6) [34,192,72,36,258] 13 := by
  apply FastRouting.sound _ _ [34,192,72,36,258] 13 (by decide) (choices 1) [1,4,16] r38698 c38698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24706
  · exact u24707
  · exact u24708

def r38699 : Route 9 := (fun mask => (mask,id))

def c38699 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38699 : Upper (D 6) (R 6) [34,192,72,36,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,36,260] 13 (by decide) (choices 1) [1,2,16] r38699 c38699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24709
  · exact u24710
  · exact u24711

#print axioms u38699
end Delivery.IrregularNine14.P06
