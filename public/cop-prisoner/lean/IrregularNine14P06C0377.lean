import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0114
import IrregularNine14P06C0115

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22620 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 268 76 21 48 98 226 354), lower := (rows 35 131 268 76 21 48 64 128 256), losses := [] }

theorem u22620 : Upper (D 6) (R 6) [34,129,264,68,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22620 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22621 : Route 9 := (fun mask => (mask,id))

def c22621 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22621 : Upper (D 6) (R 6) [34,129,264,68,5,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,68,5,64] 13 (by decide) (choices 1) [2,16,32] r22621 c22621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6882
  · exact u6883
  · exact u6884

def b22622 : PairBound 9 := { available := 112, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 76 22 33 112 240 368), lower := (rows 35 131 268 76 22 33 64 128 256), losses := [] }

theorem u22622 : Upper (D 6) (R 6) [34,129,264,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22623 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 268 76 22 48 97 225 353), lower := (rows 35 131 268 76 22 48 64 128 256), losses := [] }

theorem u22623 : Upper (D 6) (R 6) [34,129,264,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22623 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22624 : Route 9 := (fun mask => (mask,id))

def c22624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22624 : Upper (D 6) (R 6) [34,129,264,68,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,68,6,64] 13 (by decide) (choices 1) [1,16,32] r22624 c22624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6885
  · exact u6886
  · exact u6887

def b22625 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 76 52 33 82 210 338), lower := (rows 35 131 268 76 52 33 64 128 256), losses := [] }

theorem u22625 : Upper (D 6) (R 6) [34,129,264,68,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22626 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 76 52 34 81 209 337), lower := (rows 35 131 268 76 52 34 64 128 256), losses := [] }

theorem u22626 : Upper (D 6) (R 6) [34,129,264,68,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22627 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 268 76 52 48 67 195 323), lower := (rows 35 131 268 76 52 48 64 128 256), losses := [] }

theorem u22627 : Upper (D 6) (R 6) [34,129,264,68,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22627 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22628 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 4, region := 131, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 268 76 52 96 83 147 275), lower := (rows 35 131 268 76 52 96 64 128 256), losses := [] }

theorem u22628 : Upper (D 6) (R 6) [34,129,264,68,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22629 : PairBound 9 := { available := 52, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 76 81 34 116 180 308), lower := (rows 35 131 268 76 81 34 64 128 256), losses := [] }

theorem u22629 : Upper (D 6) (R 6) [34,129,264,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22630 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 76 81 36 114 178 306), lower := (rows 35 131 268 76 81 36 64 128 256), losses := [] }

theorem u22630 : Upper (D 6) (R 6) [34,129,264,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22631 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 268 76 81 48 102 166 294), lower := (rows 35 131 268 76 81 48 64 128 256), losses := [] }

theorem u22631 : Upper (D 6) (R 6) [34,129,264,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22631 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22632 : PairBound 9 := { available := 52, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 76 82 33 116 180 308), lower := (rows 35 131 268 76 82 33 64 128 256), losses := [] }

theorem u22632 : Upper (D 6) (R 6) [34,129,264,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22633 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 76 82 36 113 177 305), lower := (rows 35 131 268 76 82 36 64 128 256), losses := [] }

theorem u22633 : Upper (D 6) (R 6) [34,129,264,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22634 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 268 76 82 48 101 165 293), lower := (rows 35 131 268 76 82 48 64 128 256), losses := [] }

theorem u22634 : Upper (D 6) (R 6) [34,129,264,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22634 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22635 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 76 112 33 86 150 278), lower := (rows 35 131 268 76 112 33 64 128 256), losses := [] }

theorem u22635 : Upper (D 6) (R 6) [34,129,264,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22636 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 76 112 34 85 149 277), lower := (rows 35 131 268 76 112 34 64 128 256), losses := [] }

theorem u22636 : Upper (D 6) (R 6) [34,129,264,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22637 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 76 112 36 83 147 275), lower := (rows 35 131 268 76 112 36 64 128 256), losses := [] }

theorem u22637 : Upper (D 6) (R 6) [34,129,264,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22638 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 268 76 112 48 71 135 263), lower := (rows 35 131 268 76 112 48 64 128 256), losses := [] }

theorem u22638 : Upper (D 6) (R 6) [34,129,264,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22638 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22639 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 88 21 34 100 228 356), lower := (rows 35 131 268 88 21 34 64 128 256), losses := [] }

theorem u22639 : Upper (D 6) (R 6) [34,129,264,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22640 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 268 88 21 36 98 226 354), lower := (rows 35 131 268 88 21 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 60 65 129 257), good := (rows 482 450 300 124 508 36 64 128 256) }] }

theorem u22640 : Upper (D 6) (R 6) [34,129,264,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22641 : Route 9 := (fun mask => (mask,id))

def c22641 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22641 : Upper (D 6) (R 6) [34,129,264,80,5,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,80,5,64] 13 (by decide) (choices 1) [2,4,32] r22641 c22641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6888
  · exact u6889
  · exact u6890

def b22642 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 88 22 33 100 228 356), lower := (rows 35 131 268 88 22 33 64 128 256), losses := [] }

theorem u22642 : Upper (D 6) (R 6) [34,129,264,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22643 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 88 22 36 97 225 353), lower := (rows 35 131 268 88 22 36 64 128 256), losses := [] }

theorem u22643 : Upper (D 6) (R 6) [34,129,264,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22644 : Route 9 := (fun mask => (mask,id))

def c22644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22644 : Upper (D 6) (R 6) [34,129,264,80,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,80,6,64] 13 (by decide) (choices 1) [1,4,32] r22644 c22644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6891
  · exact u6892
  · exact u6893

def b22645 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 88 52 33 70 198 326), lower := (rows 35 131 268 88 52 33 64 128 256), losses := [] }

theorem u22645 : Upper (D 6) (R 6) [34,129,264,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22646 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 88 52 34 69 197 325), lower := (rows 35 131 268 88 52 34 64 128 256), losses := [] }

theorem u22646 : Upper (D 6) (R 6) [34,129,264,80,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22647 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 268 88 52 36 67 195 323), lower := (rows 35 131 268 88 52 36 64 128 256), losses := [] }

theorem u22647 : Upper (D 6) (R 6) [34,129,264,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22648 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 131, targets := 64 }], pairs := [(0,6),(1,6),(4,0)], upper := (rows 35 131 268 88 52 96 71 135 263), lower := (rows 35 131 268 88 52 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 104 64 128 256), good := (rows 34 130 316 120 52 96 96 128 256) }] }

theorem u22648 : Upper (D 6) (R 6) [34,129,264,80,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22649 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 104 21 34 84 212 340), lower := (rows 35 131 268 104 21 34 64 128 256), losses := [] }

theorem u22649 : Upper (D 6) (R 6) [34,129,264,96,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22650 : Route 9 := (fun mask => (mask,id))

def c22650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22650 : Upper (D 6) (R 6) [34,129,264,96,5,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,96,5,4] 13 (by decide) (choices 1) [2,16] r22650 c22650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6894
  · exact u6895

def b22651 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 268 104 21 48 70 198 326), lower := (rows 35 131 268 104 21 48 64 128 256), losses := [] }

theorem u22651 : Upper (D 6) (R 6) [34,129,264,96,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22651 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22652 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 268 104 21 96 86 150 278), lower := (rows 35 131 268 104 21 96 64 128 256), losses := [] }

theorem u22652 : Upper (D 6) (R 6) [34,129,264,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22653 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 104 22 33 84 212 340), lower := (rows 35 131 268 104 22 33 64 128 256), losses := [] }

theorem u22653 : Upper (D 6) (R 6) [34,129,264,96,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22654 : Route 9 := (fun mask => (mask,id))

def c22654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22654 : Upper (D 6) (R 6) [34,129,264,96,6,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,96,6,4] 13 (by decide) (choices 1) [1,16] r22654 c22654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6896
  · exact u6897

def b22655 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 268 104 22 48 69 197 325), lower := (rows 35 131 268 104 22 48 64 128 256), losses := [] }

theorem u22655 : Upper (D 6) (R 6) [34,129,264,96,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22655 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22656 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 268 104 22 96 85 149 277), lower := (rows 35 131 268 104 22 96 64 128 256), losses := [] }

theorem u22656 : Upper (D 6) (R 6) [34,129,264,96,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22657 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 104 81 34 84 148 276), lower := (rows 35 131 268 104 81 34 64 128 256), losses := [] }

theorem u22657 : Upper (D 6) (R 6) [34,129,264,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22658 : Route 9 := (fun mask => (mask,id))

def c22658 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22658 : Upper (D 6) (R 6) [34,129,264,96,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,96,65,4] 13 (by decide) (choices 1) [2,4,16] r22658 c22658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6898
  · exact u6899
  · exact u6900

def b22659 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 268 104 81 48 70 134 262), lower := (rows 35 131 268 104 81 48 64 128 256), losses := [] }

theorem u22659 : Upper (D 6) (R 6) [34,129,264,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22659 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22660 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 104 82 33 84 148 276), lower := (rows 35 131 268 104 82 33 64 128 256), losses := [] }

theorem u22660 : Upper (D 6) (R 6) [34,129,264,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22661 : Route 9 := (fun mask => (mask,id))

def c22661 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22661 : Upper (D 6) (R 6) [34,129,264,96,66,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,96,66,4] 13 (by decide) (choices 1) [1,4,16] r22661 c22661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6901
  · exact u6902
  · exact u6903

def b22662 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 268 104 82 48 69 133 261), lower := (rows 35 131 268 104 82 48 64 128 256), losses := [] }

theorem u22662 : Upper (D 6) (R 6) [34,129,264,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22662 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22663 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 104 84 33 86 150 278), lower := (rows 35 131 268 104 84 33 64 128 256), losses := [] }

theorem u22663 : Upper (D 6) (R 6) [34,129,264,96,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22664 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 104 84 34 85 149 277), lower := (rows 35 131 268 104 84 34 64 128 256), losses := [] }

theorem u22664 : Upper (D 6) (R 6) [34,129,264,96,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22665 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 40, targets := 3 },{ cop := 4, region := 163, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 35 131 268 104 84 36 83 147 275), lower := (rows 35 131 268 104 84 36 64 128 256), losses := [] }

theorem u22665 : Upper (D 6) (R 6) [34,129,264,96,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22666 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 268 104 84 48 71 135 263), lower := (rows 35 131 268 104 84 48 64 128 256), losses := [] }

theorem u22666 : Upper (D 6) (R 6) [34,129,264,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22666 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22667 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 292 13 22 40 80 208 336), lower := (rows 35 131 292 13 22 40 64 128 256), losses := [] }

theorem u22667 : Upper (D 6) (R 6) [34,129,288,5,6,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22667 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22668 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 292 13 22 48 72 200 328), lower := (rows 35 131 292 13 22 48 64 128 256), losses := [] }

theorem u22668 : Upper (D 6) (R 6) [34,129,288,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22668 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22669 : Route 9 := (fun mask => (mask,id))

def c22669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22669 : Upper (D 6) (R 6) [34,129,288,5,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,288,5,6,64] 13 (by decide) (choices 1) [8,16] r22669 c22669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6904
  · exact u6905

def b22670 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 292 13 82 36 88 216 344), lower := (rows 35 131 292 13 82 36 64 128 256), losses := [] }

theorem u22670 : Upper (D 6) (R 6) [34,129,288,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22671 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 292 13 82 40 84 212 340), lower := (rows 35 131 292 13 82 40 64 128 256), losses := [] }

theorem u22671 : Upper (D 6) (R 6) [34,129,288,5,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22671 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22672 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 292 13 82 48 76 204 332), lower := (rows 35 131 292 13 82 48 64 128 256), losses := [] }

theorem u22672 : Upper (D 6) (R 6) [34,129,288,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22672 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22673 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 35 131 292 13 82 96 92 156 284), lower := (rows 35 131 292 13 82 96 64 128 256), losses := [] }

theorem u22673 : Upper (D 6) (R 6) [34,129,288,5,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22674 : PairBound 9 := { available := 88, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 13 84 34 88 216 344), lower := (rows 35 131 292 13 84 34 64 128 256), losses := [] }

theorem u22674 : Upper (D 6) (R 6) [34,129,288,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22675 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 292 13 84 40 82 210 338), lower := (rows 35 131 292 13 84 40 64 128 256), losses := [] }

theorem u22675 : Upper (D 6) (R 6) [34,129,288,5,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22675 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22676 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 131 292 13 84 48 74 202 330), lower := (rows 35 131 292 13 84 48 64 128 256), losses := [] }

theorem u22676 : Upper (D 6) (R 6) [34,129,288,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22676 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22677 : Route 9 := (fun mask => (mask,id))

def c22677 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22677 : Upper (D 6) (R 6) [34,129,288,5,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,288,5,68,64] 13 (by decide) (choices 1) [2,8,16] r22677 c22677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6906
  · exact u6907
  · exact u6908

def b22678 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 292 13 88 34 84 212 340), lower := (rows 35 131 292 13 88 34 64 128 256), losses := [] }

theorem u22678 : Upper (D 6) (R 6) [34,129,288,5,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22679 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 292 13 88 36 82 210 338), lower := (rows 35 131 292 13 88 36 64 128 256), losses := [] }

theorem u22679 : Upper (D 6) (R 6) [34,129,288,5,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u22679
end Delivery.IrregularNine14.P06
