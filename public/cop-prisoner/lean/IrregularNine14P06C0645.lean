import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0411
import IrregularNine14P06C0412
import IrregularNine14P06C0413

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b38700 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 76 56 19 293 325 389 261), lower := (rows 35 194 76 56 19 32 64 128 256), losses := [] }

theorem u38700 : Upper (D 6) (R 6) [34,192,72,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38701 : Route 9 := (fun mask => (mask,id))

def c38701 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38701 : Upper (D 6) (R 6) [34,192,72,48,5] 13 := by
  apply FastRouting.sound _ _ [34,192,72,48,5] 13 (by decide) (choices 1) [1,2,4,256] r38701 c38701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24712
  · exact u24713
  · exact u24714
  · exact u24715

def r38702 : Route 9 := (fun mask => (mask,id))

def c38702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38702 : Upper (D 6) (R 6) [34,192,72,48,6] 13 := by
  apply FastRouting.sound _ _ [34,192,72,48,6] 13 (by decide) (choices 1) [1,4,256] r38702 c38702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24716
  · exact u24717
  · exact u24718

def r38703 : Route 9 := (fun mask => (mask,id))

def c38703 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38703 : Upper (D 6) (R 6) [34,192,72,48,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,48,257] 13 (by decide) (choices 1) [1,2,4] r38703 c38703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24719
  · exact u24720
  · exact u24721

def r38704 : Route 9 := (fun mask => (mask,id))

def c38704 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38704 : Upper (D 6) (R 6) [34,192,72,48,258] 13 := by
  apply FastRouting.sound _ _ [34,192,72,48,258] 13 (by decide) (choices 1) [1,4] r38704 c38704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24722
  · exact u24723

def r38705 : Route 9 := (fun mask => (mask,id))

def c38705 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38705 : Upper (D 6) (R 6) [34,192,72,48,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,48,260] 13 (by decide) (choices 1) [1,2,4] r38705 c38705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24724
  · exact u24725
  · exact u24726

def b38706 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 76 265 19 52 116 180 308), lower := (rows 35 194 76 265 19 32 64 128 256), losses := [] }

theorem u38706 : Upper (D 6) (R 6) [34,192,72,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38707 : Route 9 := (fun mask => (mask,id))

def c38707 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38707 : Upper (D 6) (R 6) [34,192,72,257,5] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,5] 13 (by decide) (choices 1) [2,4,16] r38707 c38707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24727
  · exact u24728
  · exact u24729

def r38708 : Route 9 := (fun mask => (mask,id))

def c38708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38708 : Upper (D 6) (R 6) [34,192,72,257,6] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,6] 13 (by decide) (choices 1) [1,4,16] r38708 c38708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24730
  · exact u24731
  · exact u24732

def b38709 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 76 265 49 54 86 150 278), lower := (rows 35 194 76 265 49 32 64 128 256), losses := [] }

theorem u38709 : Upper (D 6) (R 6) [34,192,72,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38710 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 194 76 265 50 53 85 149 277), lower := (rows 35 194 76 265 50 32 64 128 256), losses := [] }

theorem u38710 : Upper (D 6) (R 6) [34,192,72,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38711 : Route 9 := (fun mask => (mask,id))

def c38711 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38711 : Upper (D 6) (R 6) [34,192,72,257,36] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,36] 13 (by decide) (choices 1) [1,2,4,16] r38711 c38711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24733
  · exact u24734
  · exact u24735
  · exact u24736

def r38712 : Route 9 := (fun mask => (mask,id))

def c38712 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38712 : Upper (D 6) (R 6) [34,192,72,258,5] 13 := by
  apply FastRouting.sound _ _ [34,192,72,258,5] 13 (by decide) (choices 1) [1,4,16] r38712 c38712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24737
  · exact u24738
  · exact u24739

def b38713 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 76 266 49 53 85 149 277), lower := (rows 35 194 76 266 49 32 64 128 256), losses := [] }

theorem u38713 : Upper (D 6) (R 6) [34,192,72,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38714 : Route 9 := (fun mask => (mask,id))

def c38714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38714 : Upper (D 6) (R 6) [34,192,72,258,36] 13 := by
  apply FastRouting.sound _ _ [34,192,72,258,36] 13 (by decide) (choices 1) [1,4,16] r38714 c38714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24740
  · exact u24741
  · exact u24742

def b38715 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 76 268 19 53 117 181 309), lower := (rows 35 194 76 268 19 32 64 128 256), losses := [] }

theorem u38715 : Upper (D 6) (R 6) [34,192,72,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38716 : Route 9 := (fun mask => (mask,id))

def c38716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38716 : Upper (D 6) (R 6) [34,192,72,260,5] 13 := by
  apply FastRouting.sound _ _ [34,192,72,260,5] 13 (by decide) (choices 1) [1,2,16] r38716 c38716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24743
  · exact u24744
  · exact u24745

def b38717 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 227, targets := 4 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 76 268 22 49 113 177 305), lower := (rows 35 194 76 268 22 32 64 128 256), losses := [] }

theorem u38717 : Upper (D 6) (R 6) [34,192,72,260,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38718 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 76 268 49 55 87 151 279), lower := (rows 35 194 76 268 49 32 64 128 256), losses := [] }

theorem u38718 : Upper (D 6) (R 6) [34,192,72,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38719 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 194 76 268 50 53 85 149 277), lower := (rows 35 194 76 268 50 32 64 128 256), losses := [] }

theorem u38719 : Upper (D 6) (R 6) [34,192,72,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38720 : Route 9 := (fun mask => (mask,id))

def c38720 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38720 : Upper (D 6) (R 6) [34,192,72,260,36] 13 := by
  apply FastRouting.sound _ _ [34,192,72,260,36] 13 (by decide) (choices 1) [1,2,16] r38720 c38720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24746
  · exact u24747
  · exact u24748

def b38721 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 76 280 19 37 101 165 293), lower := (rows 35 194 76 280 19 32 64 128 256), losses := [] }

theorem u38721 : Upper (D 6) (R 6) [34,192,72,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38722 : Route 9 := (fun mask => (mask,id))

def c38722 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38722 : Upper (D 6) (R 6) [34,192,72,272,5] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,5] 13 (by decide) (choices 1) [1,2,4] r38722 c38722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24749
  · exact u24750
  · exact u24751

def r38723 : Route 9 := (fun mask => (mask,id))

def c38723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38723 : Upper (D 6) (R 6) [34,192,72,272,6] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,6] 13 (by decide) (choices 1) [1,4] r38723 c38723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24752
  · exact u24753

def b38724 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 76 280 49 39 71 135 263), lower := (rows 35 194 76 280 49 32 64 128 256), losses := [] }

theorem u38724 : Upper (D 6) (R 6) [34,192,72,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38725 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 194 76 280 50 37 69 133 261), lower := (rows 35 194 76 280 50 32 64 128 256), losses := [] }

theorem u38725 : Upper (D 6) (R 6) [34,192,72,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38726 : Route 9 := (fun mask => (mask,id))

def c38726 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38726 : Upper (D 6) (R 6) [34,192,72,272,36] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,36] 13 (by decide) (choices 1) [1,2,4] r38726 c38726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24754
  · exact u24755
  · exact u24756

def b38727 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 76 296 19 53 85 149 277), lower := (rows 35 194 76 296 19 32 64 128 256), losses := [] }

theorem u38727 : Upper (D 6) (R 6) [34,192,72,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38728 : Route 9 := (fun mask => (mask,id))

def c38728 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38728 : Upper (D 6) (R 6) [34,192,72,288,5] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,5] 13 (by decide) (choices 1) [1,2,4,16] r38728 c38728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24757
  · exact u24758
  · exact u24759
  · exact u24760

def r38729 : Route 9 := (fun mask => (mask,id))

def c38729 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38729 : Upper (D 6) (R 6) [34,192,72,288,6] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,6] 13 (by decide) (choices 1) [1,4,16] r38729 c38729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24761
  · exact u24762
  · exact u24763

def b38730 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 100 11 21 316 348 412 284), lower := (rows 35 194 100 11 21 32 64 128 256), losses := [] }

theorem u38730 : Upper (D 6) (R 6) [34,192,96,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38731 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 100 11 25 308 340 404 276), lower := (rows 35 194 100 11 25 32 64 128 256), losses := [] }

theorem u38731 : Upper (D 6) (R 6) [34,192,96,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38732 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 100 11 28 309 341 405 277), lower := (rows 35 194 100 11 28 32 64 128 256), losses := [] }

theorem u38732 : Upper (D 6) (R 6) [34,192,96,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38733 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 100 11 273 60 92 156 284), lower := (rows 35 194 100 11 273 32 64 128 256), losses := [] }

theorem u38733 : Upper (D 6) (R 6) [34,192,96,3,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38734 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 100 11 276 61 93 157 285), lower := (rows 35 194 100 11 276 32 64 128 256), losses := [] }

theorem u38734 : Upper (D 6) (R 6) [34,192,96,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38735 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 100 11 280 53 85 149 277), lower := (rows 35 194 100 11 280 32 64 128 256), losses := [] }

theorem u38735 : Upper (D 6) (R 6) [34,192,96,3,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38736 : PairBound 9 := { available := 282, camps := [{ cop := 3, region := 16, targets := 66 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 35 194 100 13 21 314 346 410 282), lower := (rows 35 194 100 13 21 32 64 128 256), losses := [] }

theorem u38736 : Upper (D 6) (R 6) [34,192,96,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38737 : PairBound 9 := { available := 281, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6),(1,5),(4,5)], upper := (rows 35 194 100 13 22 313 345 409 281), lower := (rows 35 194 100 13 22 32 64 128 256), losses := [] }

theorem u38737 : Upper (D 6) (R 6) [34,192,96,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38738 : PairBound 9 := { available := 278, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 100 13 25 310 342 406 278), lower := (rows 35 194 100 13 25 32 64 128 256), losses := [] }

theorem u38738 : Upper (D 6) (R 6) [34,192,96,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38739 : Route 9 := (fun mask => (mask,id))

def c38739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38739 : Upper (D 6) (R 6) [34,192,96,5,10] 13 := by
  apply FastRouting.sound _ _ [34,192,96,5,10] 13 (by decide) (choices 1) [1,4,16,256] r38739 c38739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24764
  · exact u24765
  · exact u24766
  · exact u24767

def b38740 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 100 13 28 307 339 403 275), lower := (rows 35 194 100 13 28 32 64 128 256), losses := [] }

theorem u38740 : Upper (D 6) (R 6) [34,192,96,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38741 : Route 9 := (fun mask => (mask,id))

def c38741 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38741 : Upper (D 6) (R 6) [34,192,96,5,257] 13 := by
  apply FastRouting.sound _ _ [34,192,96,5,257] 13 (by decide) (choices 1) [2,4,8,16] r38741 c38741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24768
  · exact u24769
  · exact u24770
  · exact u24771

def r38742 : Route 9 := (fun mask => (mask,id))

def c38742 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38742 : Upper (D 6) (R 6) [34,192,96,5,258] 13 := by
  apply FastRouting.sound _ _ [34,192,96,5,258] 13 (by decide) (choices 1) [1,4,8,16] r38742 c38742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24772
  · exact u24773
  · exact u24774
  · exact u24775

def r38743 : Route 9 := (fun mask => (mask,id))

def c38743 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38743 : Upper (D 6) (R 6) [34,192,96,5,260] 13 := by
  apply FastRouting.sound _ _ [34,192,96,5,260] 13 (by decide) (choices 1) [1,2,8,16] r38743 c38743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24776
  · exact u24777
  · exact u24778
  · exact u24779

def r38744 : Route 9 := (fun mask => (mask,id))

def c38744 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38744 : Upper (D 6) (R 6) [34,192,96,5,264] 13 := by
  apply FastRouting.sound _ _ [34,192,96,5,264] 13 (by decide) (choices 1) [1,2,4,16] r38744 c38744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24780
  · exact u24781
  · exact u24782
  · exact u24783

def b38745 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 305, targets := 64 },{ cop := 4, region := 356, targets := 2 }], pairs := [(0,6),(2,1),(4,6)], upper := (rows 35 194 100 14 25 309 341 405 277), lower := (rows 35 194 100 14 25 32 64 128 256), losses := [] }

theorem u38745 : Upper (D 6) (R 6) [34,192,96,6,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38746 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 194 100 14 28 305 337 401 273), lower := (rows 35 194 100 14 28 32 64 128 256), losses := [] }

theorem u38746 : Upper (D 6) (R 6) [34,192,96,6,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38747 : Route 9 := (fun mask => (mask,id))

def c38747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38747 : Upper (D 6) (R 6) [34,192,96,6,257] 13 := by
  apply FastRouting.sound _ _ [34,192,96,6,257] 13 (by decide) (choices 1) [1,4,8,16] r38747 c38747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24784
  · exact u24785
  · exact u24786
  · exact u24787

def r38748 : Route 9 := (fun mask => (mask,id))

def c38748 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38748 : Upper (D 6) (R 6) [34,192,96,6,260] 13 := by
  apply FastRouting.sound _ _ [34,192,96,6,260] 13 (by decide) (choices 1) [1,8,16] r38748 c38748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24788
  · exact u24789
  · exact u24790

def r38749 : Route 9 := (fun mask => (mask,id))

def c38749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38749 : Upper (D 6) (R 6) [34,192,96,6,264] 13 := by
  apply FastRouting.sound _ _ [34,192,96,6,264] 13 (by decide) (choices 1) [1,4,16] r38749 c38749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24791
  · exact u24792
  · exact u24793

def b38750 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 100 25 25 294 326 390 262), lower := (rows 35 194 100 25 25 32 64 128 256), losses := [] }

theorem u38750 : Upper (D 6) (R 6) [34,192,96,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38751 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 100 25 26 293 325 389 261), lower := (rows 35 194 100 25 26 32 64 128 256), losses := [] }

theorem u38751 : Upper (D 6) (R 6) [34,192,96,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38752 : Route 9 := (fun mask => (mask,id))

def c38752 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38752 : Upper (D 6) (R 6) [34,192,96,17,12] 13 := by
  apply FastRouting.sound _ _ [34,192,96,17,12] 13 (by decide) (choices 1) [1,2,4,256] r38752 c38752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24794
  · exact u24795
  · exact u24796
  · exact u24797

def b38753 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 100 25 273 46 78 142 270), lower := (rows 35 194 100 25 273 32 64 128 256), losses := [] }

theorem u38753 : Upper (D 6) (R 6) [34,192,96,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38754 : Route 9 := (fun mask => (mask,id))

def c38754 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38754 : Upper (D 6) (R 6) [34,192,96,17,258] 13 := by
  apply FastRouting.sound _ _ [34,192,96,17,258] 13 (by decide) (choices 1) [1,4,8] r38754 c38754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24798
  · exact u24799
  · exact u24800

def r38755 : Route 9 := (fun mask => (mask,id))

def c38755 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38755 : Upper (D 6) (R 6) [34,192,96,17,260] 13 := by
  apply FastRouting.sound _ _ [34,192,96,17,260] 13 (by decide) (choices 1) [1,2,4,8] r38755 c38755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24801
  · exact u24802
  · exact u24803
  · exact u24804

def r38756 : Route 9 := (fun mask => (mask,id))

def c38756 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38756 : Upper (D 6) (R 6) [34,192,96,17,264] 13 := by
  apply FastRouting.sound _ _ [34,192,96,17,264] 13 (by decide) (choices 1) [1,2,4] r38756 c38756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24805
  · exact u24806
  · exact u24807

def r38757 : Route 9 := (fun mask => (mask,id))

def c38757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38757 : Upper (D 6) (R 6) [34,192,96,18,12] 13 := by
  apply FastRouting.sound _ _ [34,192,96,18,12] 13 (by decide) (choices 1) [1,4,256] r38757 c38757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24808
  · exact u24809
  · exact u24810

def r38758 : Route 9 := (fun mask => (mask,id))

def c38758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38758 : Upper (D 6) (R 6) [34,192,96,18,257] 13 := by
  apply FastRouting.sound _ _ [34,192,96,18,257] 13 (by decide) (choices 1) [1,4,8] r38758 c38758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24811
  · exact u24812
  · exact u24813

def r38759 : Route 9 := (fun mask => (mask,id))

def c38759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38759 : Upper (D 6) (R 6) [34,192,96,18,260] 13 := by
  apply FastRouting.sound _ _ [34,192,96,18,260] 13 (by decide) (choices 1) [1,4,8] r38759 c38759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24814
  · exact u24815
  · exact u24816

#print axioms u38759
end Delivery.IrregularNine14.P06
