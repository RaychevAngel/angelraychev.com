import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0145
import IrregularNine14P06C0146

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27600 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 25 82 36 71 135 263), lower := (rows 97 138 292 25 82 36 64 128 256), losses := [] }

theorem u27600 : Upper (D 6) (R 6) [96,136,288,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27601 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 138 292 25 84 33 70 134 262), lower := (rows 97 138 292 25 84 33 64 128 256), losses := [] }

theorem u27601 : Upper (D 6) (R 6) [96,136,288,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27602 : Route 9 := (fun mask => (mask,id))

def c27602 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27602 : Upper (D 6) (R 6) [96,136,288,17,68,2] 13 := by
  apply FastRouting.sound _ _ [96,136,288,17,68,2] 13 (by decide) (choices 1) [1,2,4] r27602 c27602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8737
  · exact u8738
  · exact u8739

def b27603 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 25 84 36 67 131 259), lower := (rows 97 138 292 25 84 36 64 128 256), losses := [] }

theorem u27603 : Upper (D 6) (R 6) [96,136,288,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27604 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 97 138 292 26 21 33 70 198 326), lower := (rows 97 138 292 26 21 33 64 128 256), losses := [] }

theorem u27604 : Upper (D 6) (R 6) [96,136,288,18,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27605 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 341, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 292 26 21 34 69 197 325), lower := (rows 97 138 292 26 21 34 64 128 256), losses := [] }

theorem u27605 : Upper (D 6) (R 6) [96,136,288,18,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27606 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 202, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 97 138 292 26 21 36 67 195 323), lower := (rows 97 138 292 26 21 36 64 128 256), losses := [] }

theorem u27606 : Upper (D 6) (R 6) [96,136,288,18,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27607 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 292 26 21 96 71 135 263), lower := (rows 97 138 292 26 21 96 64 128 256), losses := [] }

theorem u27607 : Upper (D 6) (R 6) [96,136,288,18,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27608 : Route 9 := (fun mask => (mask,id))

def c27608 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27608 : Upper (D 6) (R 6) [96,136,288,18,68,1] 13 := by
  apply FastRouting.sound _ _ [96,136,288,18,68,1] 13 (by decide) (choices 1) [1,2,4] r27608 c27608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8740
  · exact u8741
  · exact u8742

def b27609 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 341, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 292 26 84 34 69 133 261), lower := (rows 97 138 292 26 84 34 64 128 256), losses := [] }

theorem u27609 : Upper (D 6) (R 6) [96,136,288,18,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27610 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 26 84 36 67 131 259), lower := (rows 97 138 292 26 84 36 64 128 256), losses := [] }

theorem u27610 : Upper (D 6) (R 6) [96,136,288,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27611 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 194, targets := 33 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(1,5)], upper := (rows 97 138 292 28 19 33 70 198 326), lower := (rows 97 138 292 28 19 33 64 128 256), losses := [] }

theorem u27611 : Upper (D 6) (R 6) [96,136,288,20,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27612 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 325, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 138 292 28 19 34 69 197 325), lower := (rows 97 138 292 28 19 34 64 128 256), losses := [{ target := 1, region := (rows 37 0 37 24 16 32 125 189 317), good := (rows 485 456 485 477 477 485 64 128 256) }] }

theorem u27612 : Upper (D 6) (R 6) [96,136,288,20,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27613 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 28 19 36 67 195 323), lower := (rows 97 138 292 28 19 36 64 128 256), losses := [] }

theorem u27613 : Upper (D 6) (R 6) [96,136,288,20,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27614 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 292 28 19 96 71 135 263), lower := (rows 97 138 292 28 19 96 64 128 256), losses := [] }

theorem u27614 : Upper (D 6) (R 6) [96,136,288,20,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27615 : Route 9 := (fun mask => (mask,id))

def c27615 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27615 : Upper (D 6) (R 6) [96,136,288,20,66,1] 13 := by
  apply FastRouting.sound _ _ [96,136,288,20,66,1] 13 (by decide) (choices 1) [1,2,4] r27615 c27615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8743
  · exact u8744
  · exact u8745

def b27616 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 325, targets := 2 },{ cop := 0, region := 260, targets := 64 }], pairs := [(0,1),(2,1),(2,6)], upper := (rows 97 138 292 28 82 34 69 133 261), lower := (rows 97 138 292 28 82 34 64 128 256), losses := [] }

theorem u27616 : Upper (D 6) (R 6) [96,136,288,20,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27617 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 28 82 36 67 131 259), lower := (rows 97 138 292 28 82 36 64 128 256), losses := [] }

theorem u27617 : Upper (D 6) (R 6) [96,136,288,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27618 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 97 138 292 74 21 33 86 150 278), lower := (rows 97 138 292 74 21 33 64 128 256), losses := [] }

theorem u27618 : Upper (D 6) (R 6) [96,136,288,66,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27619 : PairBound 9 := { available := 21, camps := [{ cop := 5, region := 341, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 292 74 21 34 85 149 277), lower := (rows 97 138 292 74 21 34 64 128 256), losses := [] }

theorem u27619 : Upper (D 6) (R 6) [96,136,288,66,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27620 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 202, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 97 138 292 74 21 36 83 147 275), lower := (rows 97 138 292 74 21 36 64 128 256), losses := [] }

theorem u27620 : Upper (D 6) (R 6) [96,136,288,66,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27621 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 97 138 292 74 21 48 71 135 263), lower := (rows 97 138 292 74 21 48 64 128 256), losses := [] }

theorem u27621 : Upper (D 6) (R 6) [96,136,288,66,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27621 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27622 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 4, region := 357, targets := 2 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 97 138 292 74 22 33 85 149 277), lower := (rows 97 138 292 74 22 33 64 128 256), losses := [] }

theorem u27622 : Upper (D 6) (R 6) [96,136,288,66,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27623 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 74 22 36 81 145 273), lower := (rows 97 138 292 74 22 36 64 128 256), losses := [] }

theorem u27623 : Upper (D 6) (R 6) [96,136,288,66,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27624 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 357, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 97 138 292 74 22 48 69 133 261), lower := (rows 97 138 292 74 22 48 64 128 256), losses := [] }

theorem u27624 : Upper (D 6) (R 6) [96,136,288,66,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27624 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27625 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 4, region := 292, targets := 64 }], pairs := [(0,1),(0,2),(2,6)], upper := (rows 97 138 292 76 19 33 86 150 278), lower := (rows 97 138 292 76 19 33 64 128 256), losses := [] }

theorem u27625 : Upper (D 6) (R 6) [96,136,288,68,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27626 : Route 9 := (fun mask => (mask,id))

def c27626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27626 : Upper (D 6) (R 6) [96,136,288,68,3,2] 13 := by
  apply FastRouting.sound _ _ [96,136,288,68,3,2] 13 (by decide) (choices 1) [1,4,16] r27626 c27626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8746
  · exact u8747
  · exact u8748

def b27627 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 76 19 36 83 147 275), lower := (rows 97 138 292 76 19 36 64 128 256), losses := [] }

theorem u27627 : Upper (D 6) (R 6) [96,136,288,68,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27628 : Route 9 := (fun mask => (mask,id))

def c27628 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27628 : Upper (D 6) (R 6) [96,136,288,68,3,16] 13 := by
  apply FastRouting.sound _ _ [96,136,288,68,3,16] 13 (by decide) (choices 1) [1,2,4] r27628 c27628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8749
  · exact u8750
  · exact u8751

def b27629 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 97 138 292 76 21 33 82 146 274), lower := (rows 97 138 292 76 21 33 64 128 256), losses := [] }

theorem u27629 : Upper (D 6) (R 6) [96,136,288,68,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27630 : Route 9 := (fun mask => (mask,id))

def c27630 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27630 : Upper (D 6) (R 6) [96,136,288,68,5,2] 13 := by
  apply FastRouting.sound _ _ [96,136,288,68,5,2] 13 (by decide) (choices 1) [1,2,16] r27630 c27630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8752
  · exact u8753
  · exact u8754

def b27631 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 49, targets := 2 }], pairs := [(0,1),(4,1)], upper := (rows 97 138 292 76 21 48 67 131 259), lower := (rows 97 138 292 76 21 48 64 128 256), losses := [] }

theorem u27631 : Upper (D 6) (R 6) [96,136,288,68,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27631 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27632 : Route 9 := (fun mask => (mask,id))

def c27632 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27632 : Upper (D 6) (R 6) [96,136,288,68,6,1] 13 := by
  apply FastRouting.sound _ _ [96,136,288,68,6,1] 13 (by decide) (choices 1) [1,2,16] r27632 c27632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8755
  · exact u8756
  · exact u8757

def r27633 : Route 9 := (fun mask => (mask,id))

def c27633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27633 : Upper (D 6) (R 6) [96,136,288,68,6,2] 13 := by
  apply FastRouting.sound _ _ [96,136,288,68,6,2] 13 (by decide) (choices 1) [1,16] r27633 c27633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8758
  · exact u8759

def r27634 : Route 9 := (fun mask => (mask,id))

def c27634 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27634 : Upper (D 6) (R 6) [96,136,288,68,6,16] 13 := by
  apply FastRouting.sound _ _ [96,136,288,68,6,16] 13 (by decide) (choices 1) [1,2] r27634 c27634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8760
  · exact u8761

def b27635 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 4, region := 292, targets := 64 }], pairs := [(0,1),(0,2),(2,6)], upper := (rows 97 138 292 88 19 33 70 134 262), lower := (rows 97 138 292 88 19 33 64 128 256), losses := [] }

theorem u27635 : Upper (D 6) (R 6) [96,136,288,80,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27636 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 325, targets := 2 },{ cop := 0, region := 260, targets := 64 }], pairs := [(0,1),(2,1),(2,6)], upper := (rows 97 138 292 88 19 34 69 133 261), lower := (rows 97 138 292 88 19 34 64 128 256), losses := [] }

theorem u27636 : Upper (D 6) (R 6) [96,136,288,80,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27637 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 88 19 36 71 135 263), lower := (rows 97 138 292 88 19 36 64 128 256), losses := [] }

theorem u27637 : Upper (D 6) (R 6) [96,136,288,80,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27638 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 97 138 292 88 21 33 70 134 262), lower := (rows 97 138 292 88 21 33 64 128 256), losses := [] }

theorem u27638 : Upper (D 6) (R 6) [96,136,288,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27639 : Route 9 := (fun mask => (mask,id))

def c27639 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27639 : Upper (D 6) (R 6) [96,136,288,80,5,2] 13 := by
  apply FastRouting.sound _ _ [96,136,288,80,5,2] 13 (by decide) (choices 1) [1,2,4] r27639 c27639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8762
  · exact u8763
  · exact u8764

def b27640 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 202, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 97 138 292 88 21 36 67 131 259), lower := (rows 97 138 292 88 21 36 64 128 256), losses := [] }

theorem u27640 : Upper (D 6) (R 6) [96,136,288,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27641 : Route 9 := (fun mask => (mask,id))

def c27641 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27641 : Upper (D 6) (R 6) [96,136,288,80,6,1] 13 := by
  apply FastRouting.sound _ _ [96,136,288,80,6,1] 13 (by decide) (choices 1) [1,2,4] r27641 c27641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8765
  · exact u8766
  · exact u8767

def b27642 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 325, targets := 2 },{ cop := 0, region := 260, targets := 64 }], pairs := [(0,1),(2,1),(2,6)], upper := (rows 97 138 292 88 22 34 69 133 261), lower := (rows 97 138 292 88 22 34 64 128 256), losses := [] }

theorem u27642 : Upper (D 6) (R 6) [96,136,288,80,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27643 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 88 22 36 67 131 259), lower := (rows 97 138 292 88 22 36 64 128 256), losses := [] }

theorem u27643 : Upper (D 6) (R 6) [96,136,288,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27644 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 340, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 97 162 324 11 22 33 92 156 284), lower := (rows 97 162 324 11 22 33 64 128 256), losses := [] }

theorem u27644 : Upper (D 6) (R 6) [96,160,320,3,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27645 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 340, targets := 32 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(2,5),(4,5)], upper := (rows 97 162 324 11 22 36 89 153 281), lower := (rows 97 162 324 11 22 36 64 128 256), losses := [] }

theorem u27645 : Upper (D 6) (R 6) [96,160,320,3,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27646 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 97 162 324 11 22 40 85 149 277), lower := (rows 97 162 324 11 22 40 64 128 256), losses := [] }

theorem u27646 : Upper (D 6) (R 6) [96,160,320,3,6,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27646 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27647 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 97 162 324 11 22 48 77 141 269), lower := (rows 97 162 324 11 22 48 64 128 256), losses := [] }

theorem u27647 : Upper (D 6) (R 6) [96,160,320,3,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27647 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27648 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 340, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 97 162 324 11 28 33 86 150 278), lower := (rows 97 162 324 11 28 33 64 128 256), losses := [] }

theorem u27648 : Upper (D 6) (R 6) [96,160,320,3,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27649 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 97 162 324 11 28 34 85 149 277), lower := (rows 97 162 324 11 28 34 64 128 256), losses := [] }

theorem u27649 : Upper (D 6) (R 6) [96,160,320,3,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27650 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 340, targets := 32 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(2,5),(4,5)], upper := (rows 97 162 324 11 28 36 83 147 275), lower := (rows 97 162 324 11 28 36 64 128 256), losses := [] }

theorem u27650 : Upper (D 6) (R 6) [96,160,320,3,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27651 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 97 162 324 11 28 48 71 135 263), lower := (rows 97 162 324 11 28 48 64 128 256), losses := [] }

theorem u27651 : Upper (D 6) (R 6) [96,160,320,3,12,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27651 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27652 : PairBound 9 := { available := 22, camps := [{ cop := 6, region := 33, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 97 162 324 14 25 33 86 150 278), lower := (rows 97 162 324 14 25 33 64 128 256), losses := [{ target := 1, region := (rows 69 0 4 8 24 125 64 128 256), good := (rows 97 160 357 61 57 33 97 128 256) }] }

theorem u27652 : Upper (D 6) (R 6) [96,160,320,6,9,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27653 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 97 162 324 14 25 34 85 149 277), lower := (rows 97 162 324 14 25 34 64 128 256), losses := [] }

theorem u27653 : Upper (D 6) (R 6) [96,160,320,6,9,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27654 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(4,1)], upper := (rows 97 162 324 14 25 36 83 147 275), lower := (rows 97 162 324 14 25 36 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 24 44 64 128 256), good := (rows 97 160 357 61 57 37 64 128 256) },{ target := 6, region := (rows 1 18 4 8 16 44 0 144 272), good := (rows 33 162 292 46 443 36 0 128 256) }] }

theorem u27654 : Upper (D 6) (R 6) [96,160,320,6,9,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m27655_1 : Upper (D 6) (R 6) [96,160,320,6,9,16,1] 13 :=
  permutation_upper _ _ _ [96,160,320,6,9,1,16] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8768

theorem m27655_2 : Upper (D 6) (R 6) [96,160,320,6,9,16,2] 13 :=
  permutation_upper _ _ _ [96,160,320,6,9,4,16] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8770

theorem m27655_4 : Upper (D 6) (R 6) [96,160,320,6,9,16,4] 13 :=
  permutation_upper _ _ _ [96,160,320,6,9,2,16] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8769

def r27655 : Route 9 := (fun mask => (mask,id))

def c27655 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27655 : Upper (D 6) (R 6) [96,160,320,6,9,16] 13 := by
  apply FastRouting.sound _ _ [96,160,320,6,9,16] 13 (by decide) (choices 1) [1,2,4] r27655 c27655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m27655_1
  · exact m27655_2
  · exact m27655_4

def b27656 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 97 162 324 25 26 33 70 134 262), lower := (rows 97 162 324 25 26 33 64 128 256), losses := [] }

theorem u27656 : Upper (D 6) (R 6) [96,160,320,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27657 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 97 162 324 25 26 34 69 133 261), lower := (rows 97 162 324 25 26 34 64 128 256), losses := [] }

theorem u27657 : Upper (D 6) (R 6) [96,160,320,17,10,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27658 : Route 9 := (fun mask => (mask,id))

def c27658 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27658 : Upper (D 6) (R 6) [96,160,320,17,10,4] 13 := by
  apply FastRouting.sound _ _ [96,160,320,17,10,4] 13 (by decide) (choices 1) [1,2,4] r27658 c27658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8771
  · exact u8772
  · exact u8773

def r27659 : Route 9 := (fun mask => (mask,id))

def c27659 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27659 : Upper (D 6) (R 6) [96,160,320,18,12,1] 13 := by
  apply FastRouting.sound _ _ [96,160,320,18,12,1] 13 (by decide) (choices 1) [1,2,4] r27659 c27659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8774
  · exact u8775
  · exact u8776

#print axioms u27659
end Delivery.IrregularNine14.P06
