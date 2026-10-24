import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0115

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22680 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 131 292 13 88 48 70 198 326), lower := (rows 35 131 292 13 88 48 64 128 256), losses := [] }

theorem u22680 : Upper (D 6) (R 6) [34,129,288,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22680 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22681 : Route 9 := (fun mask => (mask,id))

def c22681 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22681 : Upper (D 6) (R 6) [34,129,288,5,72,64] 13 := by
  apply FastRouting.sound _ _ [34,129,288,5,72,64] 13 (by decide) (choices 1) [2,4,16] r22681 c22681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6909
  · exact u6910
  · exact u6911

def b22682 : PairBound 9 := { available := 80, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 14 25 36 80 208 336), lower := (rows 35 131 292 14 25 36 64 128 256), losses := [] }

theorem u22682 : Upper (D 6) (R 6) [34,129,288,6,9,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22683 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 292 14 25 48 68 196 324), lower := (rows 35 131 292 14 25 48 64 128 256), losses := [] }

theorem u22683 : Upper (D 6) (R 6) [34,129,288,6,9,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22683 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22684 : Route 9 := (fun mask => (mask,id))

def c22684 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22684 : Upper (D 6) (R 6) [34,129,288,6,9,64] 13 := by
  apply FastRouting.sound _ _ [34,129,288,6,9,64] 13 (by decide) (choices 1) [4,16] r22684 c22684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6912
  · exact u6913

def b22685 : PairBound 9 := { available := 88, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 14 81 36 88 216 344), lower := (rows 35 131 292 14 81 36 64 128 256), losses := [] }

theorem u22685 : Upper (D 6) (R 6) [34,129,288,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22686 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 292 14 81 40 84 212 340), lower := (rows 35 131 292 14 81 40 64 128 256), losses := [] }

theorem u22686 : Upper (D 6) (R 6) [34,129,288,6,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22686 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22687 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 292 14 81 48 76 204 332), lower := (rows 35 131 292 14 81 48 64 128 256), losses := [] }

theorem u22687 : Upper (D 6) (R 6) [34,129,288,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22687 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22688 : Route 9 := (fun mask => (mask,id))

def c22688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22688 : Upper (D 6) (R 6) [34,129,288,6,65,64] 13 := by
  apply FastRouting.sound _ _ [34,129,288,6,65,64] 13 (by decide) (choices 1) [4,8,16] r22688 c22688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6914
  · exact u6915
  · exact u6916

def b22689 : PairBound 9 := { available := 88, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 14 84 33 88 216 344), lower := (rows 35 131 292 14 84 33 64 128 256), losses := [] }

theorem u22689 : Upper (D 6) (R 6) [34,129,288,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22690 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 292 14 84 40 81 209 337), lower := (rows 35 131 292 14 84 40 64 128 256), losses := [] }

theorem u22690 : Upper (D 6) (R 6) [34,129,288,6,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22690 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22691 : Route 9 := (fun mask => (mask,id))

def c22691 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22691 : Upper (D 6) (R 6) [34,129,288,6,68,16] 13 := by
  apply FastRouting.sound _ _ [34,129,288,6,68,16] 13 (by decide) (choices 1) [1,8] r22691 c22691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6917
  · exact u6918

def r22692 : Route 9 := (fun mask => (mask,id))

def c22692 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22692 : Upper (D 6) (R 6) [34,129,288,6,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,288,6,68,64] 13 (by decide) (choices 1) [1,8,16] r22692 c22692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6919
  · exact u6920
  · exact u6921

def b22693 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 14 88 33 84 212 340), lower := (rows 35 131 292 14 88 33 64 128 256), losses := [] }

theorem u22693 : Upper (D 6) (R 6) [34,129,288,6,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22694 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 14 88 36 81 209 337), lower := (rows 35 131 292 14 88 36 64 128 256), losses := [] }

theorem u22694 : Upper (D 6) (R 6) [34,129,288,6,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22695 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 292 14 88 48 69 197 325), lower := (rows 35 131 292 14 88 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 13 8 24 56 67 131 259), good := (rows 485 453 292 508 124 48 64 128 256) }] }

theorem u22695 : Upper (D 6) (R 6) [34,129,288,6,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22695 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22696 : Route 9 := (fun mask => (mask,id))

def c22696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22696 : Upper (D 6) (R 6) [34,129,288,6,72,64] 13 := by
  apply FastRouting.sound _ _ [34,129,288,6,72,64] 13 (by decide) (choices 1) [1,4,16] r22696 c22696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6922
  · exact u6923
  · exact u6924

def b22697 : PairBound 9 := { available := 76, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 25 82 36 76 204 332), lower := (rows 35 131 292 25 82 36 64 128 256), losses := [] }

theorem u22697 : Upper (D 6) (R 6) [34,129,288,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22698 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 292 25 82 40 68 196 324), lower := (rows 35 131 292 25 82 40 64 128 256), losses := [] }

theorem u22698 : Upper (D 6) (R 6) [34,129,288,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22698 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22699 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 292 25 82 96 76 140 268), lower := (rows 35 131 292 25 82 96 64 128 256), losses := [] }

theorem u22699 : Upper (D 6) (R 6) [34,129,288,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22700 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 25 84 34 76 204 332), lower := (rows 35 131 292 25 84 34 64 128 256), losses := [] }

theorem u22700 : Upper (D 6) (R 6) [34,129,288,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22701 : PairBound 9 := { available := 74, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 25 84 36 74 202 330), lower := (rows 35 131 292 25 84 36 64 128 256), losses := [] }

theorem u22701 : Upper (D 6) (R 6) [34,129,288,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22702 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 292 25 84 40 70 198 326), lower := (rows 35 131 292 25 84 40 64 128 256), losses := [] }

theorem u22702 : Upper (D 6) (R 6) [34,129,288,17,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22702 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22703 : Route 9 := (fun mask => (mask,id))

def c22703 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22703 : Upper (D 6) (R 6) [34,129,288,17,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,288,17,68,64] 13 (by decide) (choices 1) [2,4,8] r22703 c22703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6925
  · exact u6926
  · exact u6927

def b22704 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 25 88 34 68 196 324), lower := (rows 35 131 292 25 88 34 64 128 256), losses := [] }

theorem u22704 : Upper (D 6) (R 6) [34,129,288,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22705 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 25 88 36 70 198 326), lower := (rows 35 131 292 25 88 36 64 128 256), losses := [] }

theorem u22705 : Upper (D 6) (R 6) [34,129,288,17,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22706 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 292 25 88 96 70 134 262), lower := (rows 35 131 292 25 88 96 64 128 256), losses := [] }

theorem u22706 : Upper (D 6) (R 6) [34,129,288,17,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22707 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 26 28 33 68 196 324), lower := (rows 35 131 292 26 28 33 64 128 256), losses := [] }

theorem u22707 : Upper (D 6) (R 6) [34,129,288,18,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22708 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 26 28 36 65 193 321), lower := (rows 35 131 292 26 28 36 64 128 256), losses := [] }

theorem u22708 : Upper (D 6) (R 6) [34,129,288,18,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22709 : Route 9 := (fun mask => (mask,id))

def c22709 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22709 : Upper (D 6) (R 6) [34,129,288,18,12,64] 13 := by
  apply FastRouting.sound _ _ [34,129,288,18,12,64] 13 (by decide) (choices 1) [1,4] r22709 c22709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6928
  · exact u6929

def b22710 : PairBound 9 := { available := 76, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 26 81 36 76 204 332), lower := (rows 35 131 292 26 81 36 64 128 256), losses := [] }

theorem u22710 : Upper (D 6) (R 6) [34,129,288,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22711 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 292 26 81 40 68 196 324), lower := (rows 35 131 292 26 81 40 64 128 256), losses := [] }

theorem u22711 : Upper (D 6) (R 6) [34,129,288,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22711 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22712 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 292 26 81 96 76 140 268), lower := (rows 35 131 292 26 81 96 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 112 64 128 256), good := (rows 35 131 288 59 113 96 96 128 256) }] }

theorem u22712 : Upper (D 6) (R 6) [34,129,288,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22713 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 26 84 33 76 204 332), lower := (rows 35 131 292 26 84 33 64 128 256), losses := [] }

theorem u22713 : Upper (D 6) (R 6) [34,129,288,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22714 : PairBound 9 := { available := 73, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 26 84 36 73 201 329), lower := (rows 35 131 292 26 84 36 64 128 256), losses := [] }

theorem u22714 : Upper (D 6) (R 6) [34,129,288,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22715 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 292 26 84 40 69 197 325), lower := (rows 35 131 292 26 84 40 64 128 256), losses := [] }

theorem u22715 : Upper (D 6) (R 6) [34,129,288,18,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22715 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22716 : Route 9 := (fun mask => (mask,id))

def c22716 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22716 : Upper (D 6) (R 6) [34,129,288,18,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,288,18,68,64] 13 (by decide) (choices 1) [1,4,8] r22716 c22716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6930
  · exact u6931
  · exact u6932

def b22717 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 26 88 33 68 196 324), lower := (rows 35 131 292 26 88 33 64 128 256), losses := [] }

theorem u22717 : Upper (D 6) (R 6) [34,129,288,18,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22718 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 26 88 36 69 197 325), lower := (rows 35 131 292 26 88 36 64 128 256), losses := [] }

theorem u22718 : Upper (D 6) (R 6) [34,129,288,18,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22719 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 292 26 88 96 69 133 261), lower := (rows 35 131 292 26 88 96 64 128 256), losses := [] }

theorem u22719 : Upper (D 6) (R 6) [34,129,288,18,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22720 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 28 81 34 76 204 332), lower := (rows 35 131 292 28 81 34 64 128 256), losses := [] }

theorem u22720 : Upper (D 6) (R 6) [34,129,288,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22721 : PairBound 9 := { available := 74, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 28 81 36 74 202 330), lower := (rows 35 131 292 28 81 36 64 128 256), losses := [] }

theorem u22721 : Upper (D 6) (R 6) [34,129,288,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22722 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 324, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 292 28 81 40 70 198 326), lower := (rows 35 131 292 28 81 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 21 24 16 56 67 131 259), good := (rows 486 454 292 60 508 40 64 128 256) }] }

theorem u22722 : Upper (D 6) (R 6) [34,129,288,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22722 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22723 : Route 9 := (fun mask => (mask,id))

def c22723 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22723 : Upper (D 6) (R 6) [34,129,288,20,65,64] 13 := by
  apply FastRouting.sound _ _ [34,129,288,20,65,64] 13 (by decide) (choices 1) [2,4,8] r22723 c22723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6933
  · exact u6934
  · exact u6935

def b22724 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 28 82 33 76 204 332), lower := (rows 35 131 292 28 82 33 64 128 256), losses := [] }

theorem u22724 : Upper (D 6) (R 6) [34,129,288,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22725 : PairBound 9 := { available := 73, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 28 82 36 73 201 329), lower := (rows 35 131 292 28 82 36 64 128 256), losses := [] }

theorem u22725 : Upper (D 6) (R 6) [34,129,288,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22726 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 292 28 82 40 69 197 325), lower := (rows 35 131 292 28 82 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 21 24 16 56 67 131 259), good := (rows 485 453 292 60 508 40 64 128 256) }] }

theorem u22726 : Upper (D 6) (R 6) [34,129,288,20,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22726 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22727 : Route 9 := (fun mask => (mask,id))

def c22727 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22727 : Upper (D 6) (R 6) [34,129,288,20,66,64] 13 := by
  apply FastRouting.sound _ _ [34,129,288,20,66,64] 13 (by decide) (choices 1) [1,4,8] r22727 c22727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6936
  · exact u6937
  · exact u6938

def b22728 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 28 88 33 70 198 326), lower := (rows 35 131 292 28 88 33 64 128 256), losses := [] }

theorem u22728 : Upper (D 6) (R 6) [34,129,288,20,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22729 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 28 88 34 69 197 325), lower := (rows 35 131 292 28 88 34 64 128 256), losses := [] }

theorem u22729 : Upper (D 6) (R 6) [34,129,288,20,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22730 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 28 88 36 67 195 323), lower := (rows 35 131 292 28 88 36 64 128 256), losses := [] }

theorem u22730 : Upper (D 6) (R 6) [34,129,288,20,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22731 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 292 28 88 96 71 135 263), lower := (rows 35 131 292 28 88 96 64 128 256), losses := [] }

theorem u22731 : Upper (D 6) (R 6) [34,129,288,20,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22732 : PairBound 9 := { available := 28, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 73 82 36 92 156 284), lower := (rows 35 131 292 73 82 36 64 128 256), losses := [] }

theorem u22732 : Upper (D 6) (R 6) [34,129,288,65,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22733 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 292 73 82 40 84 148 276), lower := (rows 35 131 292 73 82 40 64 128 256), losses := [] }

theorem u22733 : Upper (D 6) (R 6) [34,129,288,65,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22733 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22734 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 292 73 82 48 76 140 268), lower := (rows 35 131 292 73 82 48 64 128 256), losses := [] }

theorem u22734 : Upper (D 6) (R 6) [34,129,288,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22734 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22735 : PairBound 9 := { available := 28, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 73 84 34 92 156 284), lower := (rows 35 131 292 73 84 34 64 128 256), losses := [] }

theorem u22735 : Upper (D 6) (R 6) [34,129,288,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22736 : PairBound 9 := { available := 26, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 73 84 36 90 154 282), lower := (rows 35 131 292 73 84 36 64 128 256), losses := [] }

theorem u22736 : Upper (D 6) (R 6) [34,129,288,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22737 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 292 73 84 40 86 150 278), lower := (rows 35 131 292 73 84 40 64 128 256), losses := [] }

theorem u22737 : Upper (D 6) (R 6) [34,129,288,65,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22737 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22738 : Route 9 := (fun mask => (mask,id))

def c22738 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22738 : Upper (D 6) (R 6) [34,129,288,65,68,16] 13 := by
  apply FastRouting.sound _ _ [34,129,288,65,68,16] 13 (by decide) (choices 1) [2,4,8] r22738 c22738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6939
  · exact u6940
  · exact u6941

def b22739 : PairBound 9 := { available := 28, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 74 84 33 92 156 284), lower := (rows 35 131 292 74 84 33 64 128 256), losses := [] }

theorem u22739 : Upper (D 6) (R 6) [34,129,288,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u22739
end Delivery.IrregularNine14.P06
