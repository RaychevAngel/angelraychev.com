import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0063

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15780 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 25 112 34 68 196 324), lower := (rows 11 131 292 25 112 34 64 128 256), losses := [] }

theorem u15780 : Upper (D 6) (R 6) [10,129,288,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15781 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 25 112 36 70 198 326), lower := (rows 11 131 292 25 112 36 64 128 256), losses := [] }

theorem u15781 : Upper (D 6) (R 6) [10,129,288,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15782 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 292 25 112 96 70 134 262), lower := (rows 11 131 292 25 112 96 64 128 256), losses := [] }

theorem u15782 : Upper (D 6) (R 6) [10,129,288,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15783 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 324, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 28 81 34 100 228 356), lower := (rows 11 131 292 28 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 55 24 16 35 119 183 311), good := (rows 494 486 484 476 508 486 64 128 256) }] }

theorem u15783 : Upper (D 6) (R 6) [10,129,288,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15784 : PairBound 9 := { available := 98, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 28 81 36 98 226 354), lower := (rows 11 131 292 28 81 36 64 128 256), losses := [] }

theorem u15784 : Upper (D 6) (R 6) [10,129,288,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15785 : Route 9 := (fun mask => (mask,id))

def c15785 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15785 : Upper (D 6) (R 6) [10,129,288,20,65,64] 13 := by
  apply FastRouting.sound _ _ [10,129,288,20,65,64] 13 (by decide) (choices 1) [2,4,32] r15785 c15785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3793
  · exact u3794
  · exact u3795

def b15786 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 324, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 131 292 28 82 33 100 228 356), lower := (rows 11 131 292 28 82 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 55 24 16 35 119 183 311), good := (rows 493 485 484 476 508 485 64 128 256) }] }

theorem u15786 : Upper (D 6) (R 6) [10,129,288,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15787 : PairBound 9 := { available := 97, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 28 82 36 97 225 353), lower := (rows 11 131 292 28 82 36 64 128 256), losses := [] }

theorem u15787 : Upper (D 6) (R 6) [10,129,288,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15788 : Route 9 := (fun mask => (mask,id))

def c15788 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15788 : Upper (D 6) (R 6) [10,129,288,20,66,64] 13 := by
  apply FastRouting.sound _ _ [10,129,288,20,66,64] 13 (by decide) (choices 1) [1,4,32] r15788 c15788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3796
  · exact u3797
  · exact u3798

def r15789 : Route 9 := (fun mask => (mask,id))

def c15789 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15789 : Upper (D 6) (R 6) [10,129,288,20,96,1] 13 := by
  apply FastRouting.sound _ _ [10,129,288,20,96,1] 13 (by decide) (choices 1) [2,4] r15789 c15789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3799
  · exact u3800

def r15790 : Route 9 := (fun mask => (mask,id))

def c15790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15790 : Upper (D 6) (R 6) [10,129,288,20,96,2] 13 := by
  apply FastRouting.sound _ _ [10,129,288,20,96,2] 13 (by decide) (choices 1) [1,4] r15790 c15790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3801
  · exact u3802

def b15791 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 292 28 112 36 67 195 323), lower := (rows 11 131 292 28 112 36 64 128 256), losses := [] }

theorem u15791 : Upper (D 6) (R 6) [10,129,288,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15792 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 292 28 112 96 71 135 263), lower := (rows 11 131 292 28 112 96 64 128 256), losses := [] }

theorem u15792 : Upper (D 6) (R 6) [10,129,288,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15793 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 131 292 41 84 34 84 212 340), lower := (rows 11 131 292 41 84 34 64 128 256), losses := [] }

theorem u15793 : Upper (D 6) (R 6) [10,129,288,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15794 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 41 84 36 82 210 338), lower := (rows 11 131 292 41 84 36 64 128 256), losses := [] }

theorem u15794 : Upper (D 6) (R 6) [10,129,288,33,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15795 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 131 292 41 84 48 70 198 326), lower := (rows 11 131 292 41 84 48 64 128 256), losses := [] }

theorem u15795 : Upper (D 6) (R 6) [10,129,288,33,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15795 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15796 : Route 9 := (fun mask => (mask,id))

def c15796 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15796 : Upper (D 6) (R 6) [10,129,288,33,68,64] 13 := by
  apply FastRouting.sound _ _ [10,129,288,33,68,64] 13 (by decide) (choices 1) [2,4,16] r15796 c15796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3803
  · exact u3804
  · exact u3805

def b15797 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 131 292 56 22 33 68 196 324), lower := (rows 11 131 292 56 22 33 64 128 256), losses := [] }

theorem u15797 : Upper (D 6) (R 6) [10,129,288,48,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15798 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 195, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 292 56 22 36 65 193 321), lower := (rows 11 131 292 56 22 36 64 128 256), losses := [] }

theorem u15798 : Upper (D 6) (R 6) [10,129,288,48,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15799 : Route 9 := (fun mask => (mask,id))

def c15799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15799 : Upper (D 6) (R 6) [10,129,288,48,6,64] 13 := by
  apply FastRouting.sound _ _ [10,129,288,48,6,64] 13 (by decide) (choices 1) [1,4] r15799 c15799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3806
  · exact u3807

def b15800 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 56 81 34 68 196 324), lower := (rows 11 131 292 56 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 63 24 16 35 127 191 319), good := (rows 494 486 484 508 508 486 64 128 256) }] }

theorem u15800 : Upper (D 6) (R 6) [10,129,288,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15801 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 56 81 36 70 198 326), lower := (rows 11 131 292 56 81 36 64 128 256), losses := [] }

theorem u15801 : Upper (D 6) (R 6) [10,129,288,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15802 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 292 56 81 96 70 134 262), lower := (rows 11 131 292 56 81 96 64 128 256), losses := [] }

theorem u15802 : Upper (D 6) (R 6) [10,129,288,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15803 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 131 292 56 82 33 68 196 324), lower := (rows 11 131 292 56 82 33 64 128 256), losses := [] }

theorem u15803 : Upper (D 6) (R 6) [10,129,288,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15804 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 56 82 36 69 197 325), lower := (rows 11 131 292 56 82 36 64 128 256), losses := [] }

theorem u15804 : Upper (D 6) (R 6) [10,129,288,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15805 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 292 56 82 96 69 133 261), lower := (rows 11 131 292 56 82 96 64 128 256), losses := [] }

theorem u15805 : Upper (D 6) (R 6) [10,129,288,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15806 : Route 9 := (fun mask => (mask,id))

def c15806 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15806 : Upper (D 6) (R 6) [10,129,288,48,68,1] 13 := by
  apply FastRouting.sound _ _ [10,129,288,48,68,1] 13 (by decide) (choices 1) [2,4] r15806 c15806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3808
  · exact u3809

def r15807 : Route 9 := (fun mask => (mask,id))

def c15807 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15807 : Upper (D 6) (R 6) [10,129,288,48,68,2] 13 := by
  apply FastRouting.sound _ _ [10,129,288,48,68,2] 13 (by decide) (choices 1) [1,4] r15807 c15807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3810
  · exact u3811

def b15808 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 292 56 84 36 67 195 323), lower := (rows 11 131 292 56 84 36 64 128 256), losses := [] }

theorem u15808 : Upper (D 6) (R 6) [10,129,288,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15809 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 292 56 84 96 71 135 263), lower := (rows 11 131 292 56 84 96 64 128 256), losses := [] }

theorem u15809 : Upper (D 6) (R 6) [10,129,288,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15810 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 73 84 34 116 180 308), lower := (rows 11 131 292 73 84 34 64 128 256), losses := [] }

theorem u15810 : Upper (D 6) (R 6) [10,129,288,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15811 : PairBound 9 := { available := 50, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 73 84 36 114 178 306), lower := (rows 11 131 292 73 84 36 64 128 256), losses := [] }

theorem u15811 : Upper (D 6) (R 6) [10,129,288,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15812 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 131 292 73 84 48 102 166 294), lower := (rows 11 131 292 73 84 48 64 128 256), losses := [] }

theorem u15812 : Upper (D 6) (R 6) [10,129,288,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15812 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15813 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 73 112 34 84 148 276), lower := (rows 11 131 292 73 112 34 64 128 256), losses := [] }

theorem u15813 : Upper (D 6) (R 6) [10,129,288,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15814 : PairBound 9 := { available := 22, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 73 112 36 86 150 278), lower := (rows 11 131 292 73 112 36 64 128 256), losses := [] }

theorem u15814 : Upper (D 6) (R 6) [10,129,288,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15815 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 292 73 112 48 70 134 262), lower := (rows 11 131 292 73 112 48 64 128 256), losses := [] }

theorem u15815 : Upper (D 6) (R 6) [10,129,288,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15815 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15816 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 131 292 76 21 34 112 240 368), lower := (rows 11 131 292 76 21 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 42 162 292 76 508 34 64 128 256) }] }

theorem u15816 : Upper (D 6) (R 6) [10,129,288,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15817 : Route 9 := (fun mask => (mask,id))

def c15817 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15817 : Upper (D 6) (R 6) [10,129,288,68,5,16] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,5,16] 13 (by decide) (choices 1) [2,32] r15817 c15817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3812
  · exact u3813

def r15818 : Route 9 := (fun mask => (mask,id))

def c15818 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15818 : Upper (D 6) (R 6) [10,129,288,68,5,64] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,5,64] 13 (by decide) (choices 1) [2,16,32] r15818 c15818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3814
  · exact u3815
  · exact u3816

def r15819 : Route 9 := (fun mask => (mask,id))

def c15819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15819 : Upper (D 6) (R 6) [10,129,288,68,6,1] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,6,1] 13 (by decide) (choices 1) [16,32] r15819 c15819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3817
  · exact u3818

def r15820 : Route 9 := (fun mask => (mask,id))

def c15820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15820 : Upper (D 6) (R 6) [10,129,288,68,6,16] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,6,16] 13 (by decide) (choices 1) [1,32] r15820 c15820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3819
  · exact u3820

def r15821 : Route 9 := (fun mask => (mask,id))

def c15821 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15821 : Upper (D 6) (R 6) [10,129,288,68,6,64] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,6,64] 13 (by decide) (choices 1) [1,16,32] r15821 c15821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3821
  · exact u3822
  · exact u3823

def b15822 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 76 49 34 84 212 340), lower := (rows 11 131 292 76 49 34 64 128 256), losses := [] }

theorem u15822 : Upper (D 6) (R 6) [10,129,288,68,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15823 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 76 49 36 82 210 338), lower := (rows 11 131 292 76 49 36 64 128 256), losses := [] }

theorem u15823 : Upper (D 6) (R 6) [10,129,288,68,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15824 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 131 292 76 49 48 70 198 326), lower := (rows 11 131 292 76 49 48 64 128 256), losses := [] }

theorem u15824 : Upper (D 6) (R 6) [10,129,288,68,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15824 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15825 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 390, targets := 64 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 131 292 76 49 96 86 150 278), lower := (rows 11 131 292 76 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 104 64 128 256), good := (rows 57 145 292 108 49 96 96 128 256) }] }

theorem u15825 : Upper (D 6) (R 6) [10,129,288,68,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15826 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 76 50 33 84 212 340), lower := (rows 11 131 292 76 50 33 64 128 256), losses := [] }

theorem u15826 : Upper (D 6) (R 6) [10,129,288,68,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15827 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 76 50 36 81 209 337), lower := (rows 11 131 292 76 50 36 64 128 256), losses := [] }

theorem u15827 : Upper (D 6) (R 6) [10,129,288,68,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15828 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 131 292 76 50 48 69 197 325), lower := (rows 11 131 292 76 50 48 64 128 256), losses := [] }

theorem u15828 : Upper (D 6) (R 6) [10,129,288,68,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15828 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15829 : Route 9 := (fun mask => (mask,id))

def c15829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15829 : Upper (D 6) (R 6) [10,129,288,68,34,64] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,34,64] 13 (by decide) (choices 1) [1,4,16] r15829 c15829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3824
  · exact u3825
  · exact u3826

def b15830 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 131 292 76 81 34 116 180 308), lower := (rows 11 131 292 76 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 42 162 292 76 508 34 64 128 256) }] }

theorem u15830 : Upper (D 6) (R 6) [10,129,288,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15831 : PairBound 9 := { available := 50, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 76 81 36 114 178 306), lower := (rows 11 131 292 76 81 36 64 128 256), losses := [] }

theorem u15831 : Upper (D 6) (R 6) [10,129,288,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15832 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 131 292 76 81 48 102 166 294), lower := (rows 11 131 292 76 81 48 64 128 256), losses := [] }

theorem u15832 : Upper (D 6) (R 6) [10,129,288,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15832 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15833 : PairBound 9 := { available := 52, camps := [], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 131 292 76 82 33 116 180 308), lower := (rows 11 131 292 76 82 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 80 144 272), good := (rows 41 161 292 76 508 33 64 128 256) },{ target := 6, region := (rows 1 2 20 8 16 35 0 144 272), good := (rows 43 163 292 12 438 33 0 128 256) }] }

theorem u15833 : Upper (D 6) (R 6) [10,129,288,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15834 : PairBound 9 := { available := 49, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 76 82 36 113 177 305), lower := (rows 11 131 292 76 82 36 64 128 256), losses := [] }

theorem u15834 : Upper (D 6) (R 6) [10,129,288,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15835 : Route 9 := (fun mask => (mask,id))

def c15835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15835 : Upper (D 6) (R 6) [10,129,288,68,66,16] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,66,16] 13 (by decide) (choices 1) [1,4,32] r15835 c15835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3827
  · exact u3828
  · exact u3829

def r15836 : Route 9 := (fun mask => (mask,id))

def c15836 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15836 : Upper (D 6) (R 6) [10,129,288,68,96,1] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,96,1] 13 (by decide) (choices 1) [2,4,16] r15836 c15836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3830
  · exact u3831
  · exact u3832

def r15837 : Route 9 := (fun mask => (mask,id))

def c15837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15837 : Upper (D 6) (R 6) [10,129,288,68,96,2] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,96,2] 13 (by decide) (choices 1) [1,4,16] r15837 c15837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3833
  · exact u3834
  · exact u3835

def b15838 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 76 112 36 83 147 275), lower := (rows 11 131 292 76 112 36 64 128 256), losses := [] }

theorem u15838 : Upper (D 6) (R 6) [10,129,288,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15839 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 292 76 112 48 71 135 263), lower := (rows 11 131 292 76 112 48 64 128 256), losses := [] }

theorem u15839 : Upper (D 6) (R 6) [10,129,288,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15839 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u15839
end Delivery.IrregularNine14.P06
