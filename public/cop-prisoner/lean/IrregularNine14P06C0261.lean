import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0062

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r15660 : Route 9 := (fun mask => (mask,id))

def c15660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15660 : Upper (D 6) (R 6) [10,129,96,288,66,4] 13 := by
  apply FastRouting.sound _ _ [10,129,96,288,66,4] 13 (by decide) (choices 1) [1,4,16] r15660 c15660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3721
  · exact u3722
  · exact u3723

def b15661 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 100 296 82 48 69 133 261), lower := (rows 11 131 100 296 82 48 64 128 256), losses := [] }

theorem u15661 : Upper (D 6) (R 6) [10,129,96,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15661 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15662 : Route 9 := (fun mask => (mask,id))

def c15662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15662 : Upper (D 6) (R 6) [10,129,257,20,96,2] 13 := by
  apply FastRouting.sound _ _ [10,129,257,20,96,2] 13 (by decide) (choices 1) [4,32] r15662 c15662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3724
  · exact u3725

theorem m15663_2 : Upper (D 6) (R 6) [10,129,257,20,96,4,2] 13 :=
  permutation_upper _ _ _ [10,129,257,20,96,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3724

def r15663 : Route 9 := (fun mask => (mask,id))

def c15663 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15663 : Upper (D 6) (R 6) [10,129,257,20,96,4] 13 := by
  apply FastRouting.sound _ _ [10,129,257,20,96,4] 13 (by decide) (choices 1) [2,32] r15663 c15663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m15663_2
  · exact u3726

def b15664 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 261 28 112 96 102 166 294), lower := (rows 11 131 261 28 112 96 64 128 256), losses := [] }

theorem u15664 : Upper (D 6) (R 6) [10,129,257,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15665 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 261 44 22 48 96 224 352), lower := (rows 11 131 261 44 22 48 64 128 256), losses := [] }

theorem u15665 : Upper (D 6) (R 6) [10,129,257,36,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15665 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15666 : Route 9 := (fun mask => (mask,id))

def c15666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15666 : Upper (D 6) (R 6) [10,129,257,36,6,64] 13 := by
  apply FastRouting.sound _ _ [10,129,257,36,6,64] 13 (by decide) (choices 1) [16,32] r15666 c15666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3727
  · exact u3728

def b15667 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 261 44 50 36 80 208 336), lower := (rows 11 131 261 44 50 36 64 128 256), losses := [] }

theorem u15667 : Upper (D 6) (R 6) [10,129,257,36,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15668 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 131 261 44 50 48 68 196 324), lower := (rows 11 131 261 44 50 48 64 128 256), losses := [] }

theorem u15668 : Upper (D 6) (R 6) [10,129,257,36,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15668 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15669 : Route 9 := (fun mask => (mask,id))

def c15669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15669 : Upper (D 6) (R 6) [10,129,257,36,34,64] 13 := by
  apply FastRouting.sound _ _ [10,129,257,36,34,64] 13 (by decide) (choices 1) [4,16] r15669 c15669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3729
  · exact u3730

def b15670 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 261 44 82 36 112 240 368), lower := (rows 11 131 261 44 82 36 64 128 256), losses := [] }

theorem u15670 : Upper (D 6) (R 6) [10,129,257,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15671 : PairBound 9 := { available := 100, camps := [], pairs := [(3,0),(4,0)], upper := (rows 11 131 261 44 82 48 100 228 356), lower := (rows 11 131 261 44 82 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 55 76 140 268), good := (rows 506 178 508 492 114 48 64 128 256) }] }

theorem u15671 : Upper (D 6) (R 6) [10,129,257,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15671 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15672 : Route 9 := (fun mask => (mask,id))

def c15672 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15672 : Upper (D 6) (R 6) [10,129,257,36,66,64] 13 := by
  apply FastRouting.sound _ _ [10,129,257,36,66,64] 13 (by decide) (choices 1) [4,16,32] r15672 c15672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3731
  · exact u3732
  · exact u3733

def b15673 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 11 131 261 44 84 34 112 240 368), lower := (rows 11 131 261 44 84 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 28 35 77 141 269), good := (rows 506 482 508 508 476 34 64 128 256) }] }

theorem u15673 : Upper (D 6) (R 6) [10,129,257,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15674 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 261 44 84 48 98 226 354), lower := (rows 11 131 261 44 84 48 64 128 256), losses := [] }

theorem u15674 : Upper (D 6) (R 6) [10,129,257,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15674 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15675 : Route 9 := (fun mask => (mask,id))

def c15675 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15675 : Upper (D 6) (R 6) [10,129,257,36,68,64] 13 := by
  apply FastRouting.sound _ _ [10,129,257,36,68,64] 13 (by decide) (choices 1) [2,16,32] r15675 c15675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3734
  · exact u3735
  · exact u3736

def b15676 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 11 131 261 44 112 34 84 212 340), lower := (rows 11 131 261 44 112 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 29 35 76 140 268), good := (rows 506 178 508 508 112 34 64 128 256) }] }

theorem u15676 : Upper (D 6) (R 6) [10,129,257,36,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15677 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 261 44 112 36 82 210 338), lower := (rows 11 131 261 44 112 36 64 128 256), losses := [] }

theorem u15677 : Upper (D 6) (R 6) [10,129,257,36,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15678 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 261 44 112 48 70 198 326), lower := (rows 11 131 261 44 112 48 64 128 256), losses := [] }

theorem u15678 : Upper (D 6) (R 6) [10,129,257,36,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15678 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15679 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 261 44 112 96 86 150 278), lower := (rows 11 131 261 44 112 96 64 128 256), losses := [] }

theorem u15679 : Upper (D 6) (R 6) [10,129,257,36,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15680 : Route 9 := (fun mask => (mask,id))

def c15680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15680 : Upper (D 6) (R 6) [10,129,257,48,66,4] 13 := by
  apply FastRouting.sound _ _ [10,129,257,48,66,4] 13 (by decide) (choices 1) [4,32] r15680 c15680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3737
  · exact u3738

def b15681 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 261 56 82 96 100 164 292), lower := (rows 11 131 261 56 82 96 64 128 256), losses := [] }

theorem u15681 : Upper (D 6) (R 6) [10,129,257,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15682 : Route 9 := (fun mask => (mask,id))

def c15682 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15682 : Upper (D 6) (R 6) [10,129,257,48,68,2] 13 := by
  apply FastRouting.sound _ _ [10,129,257,48,68,2] 13 (by decide) (choices 1) [4,32] r15682 c15682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3739
  · exact u3740

def b15683 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 261 56 84 36 98 226 354), lower := (rows 11 131 261 56 84 36 64 128 256), losses := [] }

theorem u15683 : Upper (D 6) (R 6) [10,129,257,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15684 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 261 56 84 96 102 166 294), lower := (rows 11 131 261 56 84 96 64 128 256), losses := [] }

theorem u15684 : Upper (D 6) (R 6) [10,129,257,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15685 : Route 9 := (fun mask => (mask,id))

def c15685 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15685 : Upper (D 6) (R 6) [10,129,257,96,6,4] 13 := by
  apply FastRouting.sound _ _ [10,129,257,96,6,4] 13 (by decide) (choices 1) [16,32] r15685 c15685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3741
  · exact u3742

def b15686 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 261 104 22 48 100 228 356), lower := (rows 11 131 261 104 22 48 64 128 256), losses := [] }

theorem u15686 : Upper (D 6) (R 6) [10,129,257,96,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15686 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15687 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 261 104 22 96 116 180 308), lower := (rows 11 131 261 104 22 96 64 128 256), losses := [] }

theorem u15687 : Upper (D 6) (R 6) [10,129,257,96,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15688 : Route 9 := (fun mask => (mask,id))

def c15688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15688 : Upper (D 6) (R 6) [10,129,257,96,34,4] 13 := by
  apply FastRouting.sound _ _ [10,129,257,96,34,4] 13 (by decide) (choices 1) [4,16] r15688 c15688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3743
  · exact u3744

def b15689 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 131 261 104 50 48 68 196 324), lower := (rows 11 131 261 104 50 48 64 128 256), losses := [] }

theorem u15689 : Upper (D 6) (R 6) [10,129,257,96,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15689 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15690 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 261 104 50 96 84 148 276), lower := (rows 11 131 261 104 50 96 64 128 256), losses := [] }

theorem u15690 : Upper (D 6) (R 6) [10,129,257,96,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15691 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 261 104 52 34 84 212 340), lower := (rows 11 131 261 104 52 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 20 35 84 148 276), good := (rows 42 162 508 104 508 34 64 128 256) }] }

theorem u15691 : Upper (D 6) (R 6) [10,129,257,96,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15692 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 261 104 52 36 82 210 338), lower := (rows 11 131 261 104 52 36 64 128 256), losses := [] }

theorem u15692 : Upper (D 6) (R 6) [10,129,257,96,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15693 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 131 261 104 52 48 70 198 326), lower := (rows 11 131 261 104 52 48 64 128 256), losses := [] }

theorem u15693 : Upper (D 6) (R 6) [10,129,257,96,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15693 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15694 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 261 104 52 96 86 150 278), lower := (rows 11 131 261 104 52 96 64 128 256), losses := [] }

theorem u15694 : Upper (D 6) (R 6) [10,129,257,96,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15695 : Route 9 := (fun mask => (mask,id))

def c15695 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15695 : Upper (D 6) (R 6) [10,129,258,20,96,1] 13 := by
  apply FastRouting.sound _ _ [10,129,258,20,96,1] 13 (by decide) (choices 1) [4,32] r15695 c15695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3745
  · exact u3746

theorem m15696_1 : Upper (D 6) (R 6) [10,129,258,20,96,4,1] 13 :=
  permutation_upper _ _ _ [10,129,258,20,96,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3745

def r15696 : Route 9 := (fun mask => (mask,id))

def c15696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15696 : Upper (D 6) (R 6) [10,129,258,20,96,4] 13 := by
  apply FastRouting.sound _ _ [10,129,258,20,96,4] 13 (by decide) (choices 1) [1,32] r15696 c15696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m15696_1
  · exact u3747

def b15697 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 262 28 112 96 101 165 293), lower := (rows 11 131 262 28 112 96 64 128 256), losses := [] }

theorem u15697 : Upper (D 6) (R 6) [10,129,258,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15698 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 131 262 44 49 36 80 208 336), lower := (rows 11 131 262 44 49 36 64 128 256), losses := [] }

theorem u15698 : Upper (D 6) (R 6) [10,129,258,36,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15699 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 131 262 44 49 48 68 196 324), lower := (rows 11 131 262 44 49 48 64 128 256), losses := [] }

theorem u15699 : Upper (D 6) (R 6) [10,129,258,36,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15699 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15700 : Route 9 := (fun mask => (mask,id))

def c15700 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15700 : Upper (D 6) (R 6) [10,129,258,36,33,64] 13 := by
  apply FastRouting.sound _ _ [10,129,258,36,33,64] 13 (by decide) (choices 1) [4,16] r15700 c15700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3748
  · exact u3749

def b15701 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 131 262 44 81 36 112 240 368), lower := (rows 11 131 262 44 81 36 64 128 256), losses := [] }

theorem u15701 : Upper (D 6) (R 6) [10,129,258,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15702 : PairBound 9 := { available := 100, camps := [], pairs := [(2,0),(3,0)], upper := (rows 11 131 262 44 81 48 100 228 356), lower := (rows 11 131 262 44 81 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 24 16 48 88 152 280), good := (rows 462 134 262 492 508 504 64 128 256) }] }

theorem u15702 : Upper (D 6) (R 6) [10,129,258,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15702 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15703 : Route 9 := (fun mask => (mask,id))

def c15703 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15703 : Upper (D 6) (R 6) [10,129,258,36,65,64] 13 := by
  apply FastRouting.sound _ _ [10,129,258,36,65,64] 13 (by decide) (choices 1) [4,16,32] r15703 c15703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3750
  · exact u3751
  · exact u3752

def b15704 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 80, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 11 131 262 44 84 33 112 240 368), lower := (rows 11 131 262 44 84 33 64 128 256), losses := [] }

theorem u15704 : Upper (D 6) (R 6) [10,129,258,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15705 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 262 44 84 48 97 225 353), lower := (rows 11 131 262 44 84 48 64 128 256), losses := [] }

theorem u15705 : Upper (D 6) (R 6) [10,129,258,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15705 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15706 : Route 9 := (fun mask => (mask,id))

def c15706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15706 : Upper (D 6) (R 6) [10,129,258,36,68,64] 13 := by
  apply FastRouting.sound _ _ [10,129,258,36,68,64] 13 (by decide) (choices 1) [1,16,32] r15706 c15706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3753
  · exact u3754
  · exact u3755

def b15707 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 80, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 11 131 262 44 112 33 84 212 340), lower := (rows 11 131 262 44 112 33 64 128 256), losses := [] }

theorem u15707 : Upper (D 6) (R 6) [10,129,258,36,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15708 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 131 262 44 112 36 81 209 337), lower := (rows 11 131 262 44 112 36 64 128 256), losses := [] }

theorem u15708 : Upper (D 6) (R 6) [10,129,258,36,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15709 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 262 44 112 48 69 197 325), lower := (rows 11 131 262 44 112 48 64 128 256), losses := [] }

theorem u15709 : Upper (D 6) (R 6) [10,129,258,36,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15709 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15710 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 262 44 112 96 85 149 277), lower := (rows 11 131 262 44 112 96 64 128 256), losses := [] }

theorem u15710 : Upper (D 6) (R 6) [10,129,258,36,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15711 : Route 9 := (fun mask => (mask,id))

def c15711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15711 : Upper (D 6) (R 6) [10,129,258,48,65,4] 13 := by
  apply FastRouting.sound _ _ [10,129,258,48,65,4] 13 (by decide) (choices 1) [4,32] r15711 c15711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3756
  · exact u3757

def b15712 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 262 56 81 96 100 164 292), lower := (rows 11 131 262 56 81 96 64 128 256), losses := [] }

theorem u15712 : Upper (D 6) (R 6) [10,129,258,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15713 : Route 9 := (fun mask => (mask,id))

def c15713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15713 : Upper (D 6) (R 6) [10,129,258,48,68,1] 13 := by
  apply FastRouting.sound _ _ [10,129,258,48,68,1] 13 (by decide) (choices 1) [4,32] r15713 c15713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3758
  · exact u3759

def b15714 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 262 56 84 36 97 225 353), lower := (rows 11 131 262 56 84 36 64 128 256), losses := [] }

theorem u15714 : Upper (D 6) (R 6) [10,129,258,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15715 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 262 56 84 96 101 165 293), lower := (rows 11 131 262 56 84 96 64 128 256), losses := [] }

theorem u15715 : Upper (D 6) (R 6) [10,129,258,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15716 : Route 9 := (fun mask => (mask,id))

def c15716 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15716 : Upper (D 6) (R 6) [10,129,258,96,5,4] 13 := by
  apply FastRouting.sound _ _ [10,129,258,96,5,4] 13 (by decide) (choices 1) [16,32] r15716 c15716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3760
  · exact u3761

def b15717 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 262 104 21 48 100 228 356), lower := (rows 11 131 262 104 21 48 64 128 256), losses := [] }

theorem u15717 : Upper (D 6) (R 6) [10,129,258,96,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15717 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15718 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 262 104 21 96 116 180 308), lower := (rows 11 131 262 104 21 96 64 128 256), losses := [] }

theorem u15718 : Upper (D 6) (R 6) [10,129,258,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15719 : Route 9 := (fun mask => (mask,id))

def c15719 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15719 : Upper (D 6) (R 6) [10,129,258,96,33,4] 13 := by
  apply FastRouting.sound _ _ [10,129,258,96,33,4] 13 (by decide) (choices 1) [4,16] r15719 c15719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3762
  · exact u3763

#print axioms u15719
end Delivery.IrregularNine14.P06
