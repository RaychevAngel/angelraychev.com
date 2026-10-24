import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0097
import IrregularNine14P06C0098

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r19620 : Route 9 := (fun mask => (mask,id))

def c19620 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19620 : Upper (D 6) (R 6) [34,65,129,48,320,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,48,320,4] 13 (by decide) (choices 1) [2,4,8] r19620 c19620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5867
  · exact u5868
  · exact u5869

def b19621 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 56 336 40 70 134 262), lower := (rows 35 67 133 56 336 40 64 128 256), losses := [] }

theorem u19621 : Upper (D 6) (R 6) [34,65,129,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19621 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19622 : Route 9 := (fun mask => (mask,id))

def c19622 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19622 : Upper (D 6) (R 6) [34,65,129,68,258,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,68,258,4] 13 (by decide) (choices 1) [8,16,32] r19622 c19622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5870
  · exact u5871
  · exact u5872

def b19623 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 133 76 274 40 116 180 308), lower := (rows 35 67 133 76 274 40 64 128 256), losses := [] }

theorem u19623 : Upper (D 6) (R 6) [34,65,129,68,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19623 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19624 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 133 76 274 48 108 172 300), lower := (rows 35 67 133 76 274 48 64 128 256), losses := [] }

theorem u19624 : Upper (D 6) (R 6) [34,65,129,68,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19624 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19625 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 76 276 34 120 184 312), lower := (rows 35 67 133 76 276 34 64 128 256), losses := [] }

theorem u19625 : Upper (D 6) (R 6) [34,65,129,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19626 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 133 76 276 40 114 178 306), lower := (rows 35 67 133 76 276 40 64 128 256), losses := [] }

theorem u19626 : Upper (D 6) (R 6) [34,65,129,68,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19626 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19627 : Route 9 := (fun mask => (mask,id))

def c19627 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19627 : Upper (D 6) (R 6) [34,65,129,68,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,129,68,260,16] 13 (by decide) (choices 1) [2,8,32] r19627 c19627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5873
  · exact u5874
  · exact u5875

def b19628 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 76 280 34 116 180 308), lower := (rows 35 67 133 76 280 34 64 128 256), losses := [] }

theorem u19628 : Upper (D 6) (R 6) [34,65,129,68,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19629 : Route 9 := (fun mask => (mask,id))

def c19629 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19629 : Upper (D 6) (R 6) [34,65,129,68,264,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,68,264,4] 13 (by decide) (choices 1) [2,16,32] r19629 c19629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5876
  · exact u5877
  · exact u5878

def r19630 : Route 9 := (fun mask => (mask,id))

def c19630 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19630 : Upper (D 6) (R 6) [34,65,129,68,264,16] 13 := by
  apply FastRouting.sound _ _ [34,65,129,68,264,16] 13 (by decide) (choices 1) [2,4,32] r19630 c19630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5879
  · exact u5880
  · exact u5881

def b19631 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 76 304 34 92 156 284), lower := (rows 35 67 133 76 304 34 64 128 256), losses := [] }

theorem u19631 : Upper (D 6) (R 6) [34,65,129,68,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19632 : Route 9 := (fun mask => (mask,id))

def c19632 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19632 : Upper (D 6) (R 6) [34,65,129,68,288,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,68,288,4] 13 (by decide) (choices 1) [2,8,16] r19632 c19632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5882
  · exact u5883
  · exact u5884

def b19633 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 133 76 304 40 86 150 278), lower := (rows 35 67 133 76 304 40 64 128 256), losses := [] }

theorem u19633 : Upper (D 6) (R 6) [34,65,129,68,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19633 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19634 : PairBound 9 := { available := 14, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 76 304 48 78 142 270), lower := (rows 35 67 133 76 304 48 64 128 256), losses := [] }

theorem u19634 : Upper (D 6) (R 6) [34,65,129,68,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19634 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19635 : Route 9 := (fun mask => (mask,id))

def c19635 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19635 : Upper (D 6) (R 6) [34,65,129,80,258,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,80,258,4] 13 (by decide) (choices 1) [4,8,32] r19635 c19635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5885
  · exact u5886
  · exact u5887

def b19636 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 133 88 274 40 100 164 292), lower := (rows 35 67 133 88 274 40 64 128 256), losses := [] }

theorem u19636 : Upper (D 6) (R 6) [34,65,129,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19636 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19637 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 88 276 34 108 172 300), lower := (rows 35 67 133 88 276 34 64 128 256), losses := [] }

theorem u19637 : Upper (D 6) (R 6) [34,65,129,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19638 : Route 9 := (fun mask => (mask,id))

def c19638 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19638 : Upper (D 6) (R 6) [34,65,129,80,260,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,80,260,4] 13 (by decide) (choices 1) [2,8,32] r19638 c19638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5888
  · exact u5889
  · exact u5890

def b19639 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 133 88 276 40 102 166 294), lower := (rows 35 67 133 88 276 40 64 128 256), losses := [] }

theorem u19639 : Upper (D 6) (R 6) [34,65,129,80,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19639 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19640 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 88 280 34 100 164 292), lower := (rows 35 67 133 88 280 34 64 128 256), losses := [] }

theorem u19640 : Upper (D 6) (R 6) [34,65,129,80,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19641 : Route 9 := (fun mask => (mask,id))

def c19641 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19641 : Upper (D 6) (R 6) [34,65,129,80,264,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,80,264,4] 13 (by decide) (choices 1) [2,4,32] r19641 c19641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5891
  · exact u5892
  · exact u5893

def b19642 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 88 304 34 76 140 268), lower := (rows 35 67 133 88 304 34 64 128 256), losses := [] }

theorem u19642 : Upper (D 6) (R 6) [34,65,129,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19643 : Route 9 := (fun mask => (mask,id))

def c19643 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19643 : Upper (D 6) (R 6) [34,65,129,80,288,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,80,288,4] 13 (by decide) (choices 1) [2,4,8] r19643 c19643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5894
  · exact u5895
  · exact u5896

def b19644 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 88 304 40 70 134 262), lower := (rows 35 67 133 88 304 40 64 128 256), losses := [] }

theorem u19644 : Upper (D 6) (R 6) [34,65,129,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19644 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19645 : Route 9 := (fun mask => (mask,id))

def c19645 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19645 : Upper (D 6) (R 6) [34,65,129,96,258,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,96,258,4] 13 (by decide) (choices 1) [4,8,16] r19645 c19645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5897
  · exact u5898
  · exact u5899

def b19646 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 104 274 40 84 148 276), lower := (rows 35 67 133 104 274 40 64 128 256), losses := [] }

theorem u19646 : Upper (D 6) (R 6) [34,65,129,96,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19646 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19647 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 133 104 274 48 76 140 268), lower := (rows 35 67 133 104 274 48 64 128 256), losses := [] }

theorem u19647 : Upper (D 6) (R 6) [34,65,129,96,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19647 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19648 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 104 276 34 92 156 284), lower := (rows 35 67 133 104 276 34 64 128 256), losses := [] }

theorem u19648 : Upper (D 6) (R 6) [34,65,129,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19649 : Route 9 := (fun mask => (mask,id))

def c19649 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19649 : Upper (D 6) (R 6) [34,65,129,96,260,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,96,260,4] 13 (by decide) (choices 1) [2,8,16] r19649 c19649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5900
  · exact u5901
  · exact u5902

def b19650 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 104 276 40 86 150 278), lower := (rows 35 67 133 104 276 40 64 128 256), losses := [] }

theorem u19650 : Upper (D 6) (R 6) [34,65,129,96,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19650 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19651 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 133 104 276 48 78 142 270), lower := (rows 35 67 133 104 276 48 64 128 256), losses := [] }

theorem u19651 : Upper (D 6) (R 6) [34,65,129,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19651 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19652 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 104 280 34 84 148 276), lower := (rows 35 67 133 104 280 34 64 128 256), losses := [] }

theorem u19652 : Upper (D 6) (R 6) [34,65,129,96,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19653 : Route 9 := (fun mask => (mask,id))

def c19653 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19653 : Upper (D 6) (R 6) [34,65,129,96,264,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,96,264,4] 13 (by decide) (choices 1) [2,4,16] r19653 c19653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5903
  · exact u5904
  · exact u5905

def b19654 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 104 280 48 70 134 262), lower := (rows 35 67 133 104 280 48 64 128 256), losses := [] }

theorem u19654 : Upper (D 6) (R 6) [34,65,129,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19654 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19655 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 140 13 22 48 352 480 352), lower := (rows 35 67 140 13 22 48 64 128 256), losses := [] }

theorem u19655 : Upper (D 6) (R 6) [34,65,136,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19655 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19656 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 13 22 96 368 432 304), lower := (rows 35 67 140 13 22 96 64 128 256), losses := [] }

theorem u19656 : Upper (D 6) (R 6) [34,65,136,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19657 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 355, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 13 22 288 112 240 368), lower := (rows 35 67 140 13 22 288 64 128 256), losses := [] }

theorem u19657 : Upper (D 6) (R 6) [34,65,136,5,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19657 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19658 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 13 52 34 336 464 336), lower := (rows 35 67 140 13 52 34 64 128 256), losses := [] }

theorem u19658 : Upper (D 6) (R 6) [34,65,136,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19659 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 140 13 52 48 322 450 322), lower := (rows 35 67 140 13 52 48 64 128 256), losses := [] }

theorem u19659 : Upper (D 6) (R 6) [34,65,136,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19659 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19660 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 13 52 96 338 402 274), lower := (rows 35 67 140 13 52 96 64 128 256), losses := [] }

theorem u19660 : Upper (D 6) (R 6) [34,65,136,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19661 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 67, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 13 52 288 82 210 338), lower := (rows 35 67 140 13 52 288 64 128 256), losses := [] }

theorem u19661 : Upper (D 6) (R 6) [34,65,136,5,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19661 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19662 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 13 84 34 368 432 304), lower := (rows 35 67 140 13 84 34 64 128 256), losses := [] }

theorem u19662 : Upper (D 6) (R 6) [34,65,136,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19663 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 140 13 84 48 354 418 290), lower := (rows 35 67 140 13 84 48 64 128 256), losses := [] }

theorem u19663 : Upper (D 6) (R 6) [34,65,136,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19663 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19664 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 291, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 13 84 288 114 178 306), lower := (rows 35 67 140 13 84 288 64 128 256), losses := [] }

theorem u19664 : Upper (D 6) (R 6) [34,65,136,5,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19664 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19665 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 13 112 34 340 404 276), lower := (rows 35 67 140 13 112 34 64 128 256), losses := [] }

theorem u19665 : Upper (D 6) (R 6) [34,65,136,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19666 : PairBound 9 := { available := 274, camps := [{ cop := 5, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 67 140 13 112 36 338 402 274), lower := (rows 35 67 140 13 112 36 64 128 256), losses := [] }

theorem u19666 : Upper (D 6) (R 6) [34,65,136,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19667 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 140 13 112 48 326 390 262), lower := (rows 35 67 140 13 112 48 64 128 256), losses := [] }

theorem u19667 : Upper (D 6) (R 6) [34,65,136,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19667 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19668 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 13 112 288 86 150 278), lower := (rows 35 67 140 13 112 288 64 128 256), losses := [] }

theorem u19668 : Upper (D 6) (R 6) [34,65,136,5,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19668 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19669 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 67 140 13 274 36 112 240 368), lower := (rows 35 67 140 13 274 36 64 128 256), losses := [] }

theorem u19669 : Upper (D 6) (R 6) [34,65,136,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19670 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 140 13 274 48 100 228 356), lower := (rows 35 67 140 13 274 48 64 128 256), losses := [] }

theorem u19670 : Upper (D 6) (R 6) [34,65,136,5,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19670 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19671 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 13 274 96 116 180 308), lower := (rows 35 67 140 13 274 96 64 128 256), losses := [] }

theorem u19671 : Upper (D 6) (R 6) [34,65,136,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19672 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 13 276 34 112 240 368), lower := (rows 35 67 140 13 276 34 64 128 256), losses := [] }

theorem u19672 : Upper (D 6) (R 6) [34,65,136,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19673 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 99, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 13 276 48 98 226 354), lower := (rows 35 67 140 13 276 48 64 128 256), losses := [] }

theorem u19673 : Upper (D 6) (R 6) [34,65,136,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19673 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19674 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 13 276 96 114 178 306), lower := (rows 35 67 140 13 276 96 64 128 256), losses := [] }

theorem u19674 : Upper (D 6) (R 6) [34,65,136,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19675 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 13 304 34 84 212 340), lower := (rows 35 67 140 13 304 34 64 128 256), losses := [] }

theorem u19675 : Upper (D 6) (R 6) [34,65,136,5,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19676 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 67 140 13 304 36 82 210 338), lower := (rows 35 67 140 13 304 36 64 128 256), losses := [] }

theorem u19676 : Upper (D 6) (R 6) [34,65,136,5,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19677 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 140 13 304 48 70 198 326), lower := (rows 35 67 140 13 304 48 64 128 256), losses := [] }

theorem u19677 : Upper (D 6) (R 6) [34,65,136,5,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19677 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19678 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 13 304 96 86 150 278), lower := (rows 35 67 140 13 304 96 64 128 256), losses := [] }

theorem u19678 : Upper (D 6) (R 6) [34,65,136,5,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19679 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 13 336 34 116 180 308), lower := (rows 35 67 140 13 336 34 64 128 256), losses := [] }

theorem u19679 : Upper (D 6) (R 6) [34,65,136,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19679
end Delivery.IrregularNine14.P06
