import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0062
import IrregularNine14P06C0063

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15720 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 131 262 104 49 48 68 196 324), lower := (rows 11 131 262 104 49 48 64 128 256), losses := [] }

theorem u15720 : Upper (D 6) (R 6) [10,129,258,96,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15720 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15721 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 262 104 49 96 84 148 276), lower := (rows 11 131 262 104 49 96 64 128 256), losses := [] }

theorem u15721 : Upper (D 6) (R 6) [10,129,258,96,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15722 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 131 262 104 52 33 84 212 340), lower := (rows 11 131 262 104 52 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 28 20 35 84 148 276), good := (rows 41 161 508 104 508 33 64 128 256) }] }

theorem u15722 : Upper (D 6) (R 6) [10,129,258,96,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15723 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 262 104 52 36 81 209 337), lower := (rows 11 131 262 104 52 36 64 128 256), losses := [] }

theorem u15723 : Upper (D 6) (R 6) [10,129,258,96,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15724 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 131 262 104 52 48 69 197 325), lower := (rows 11 131 262 104 52 48 64 128 256), losses := [] }

theorem u15724 : Upper (D 6) (R 6) [10,129,258,96,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15724 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15725 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 262 104 52 96 85 149 277), lower := (rows 11 131 262 104 52 96 64 128 256), losses := [] }

theorem u15725 : Upper (D 6) (R 6) [10,129,258,96,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15726 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 276 13 112 34 100 228 356), lower := (rows 11 131 276 13 112 34 64 128 256), losses := [] }

theorem u15726 : Upper (D 6) (R 6) [10,129,272,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m15727_2 : Upper (D 6) (R 6) [10,129,272,5,96,4,2] 13 :=
  permutation_upper _ _ _ [10,129,272,5,96,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3764

def r15727 : Route 9 := (fun mask => (mask,id))

def c15727 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15727 : Upper (D 6) (R 6) [10,129,272,5,96,4] 13 := by
  apply FastRouting.sound _ _ [10,129,272,5,96,4] 13 (by decide) (choices 1) [2,32] r15727 c15727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m15727_2
  · exact u3765

def b15728 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 276 13 112 96 102 166 294), lower := (rows 11 131 276 13 112 96 64 128 256), losses := [] }

theorem u15728 : Upper (D 6) (R 6) [10,129,272,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15729 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 131 276 41 52 34 68 196 324), lower := (rows 11 131 276 41 52 34 64 128 256), losses := [] }

theorem u15729 : Upper (D 6) (R 6) [10,129,272,33,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15730 : PairBound 9 := { available := 66, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 276 41 52 36 66 194 322), lower := (rows 11 131 276 41 52 36 64 128 256), losses := [] }

theorem u15730 : Upper (D 6) (R 6) [10,129,272,33,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15731 : Route 9 := (fun mask => (mask,id))

def c15731 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15731 : Upper (D 6) (R 6) [10,129,272,33,36,64] 13 := by
  apply FastRouting.sound _ _ [10,129,272,33,36,64] 13 (by decide) (choices 1) [2,4] r15731 c15731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3766
  · exact u3767

def b15732 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 131 276 41 84 34 100 228 356), lower := (rows 11 131 276 41 84 34 64 128 256), losses := [] }

theorem u15732 : Upper (D 6) (R 6) [10,129,272,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15733 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 276 41 84 36 98 226 354), lower := (rows 11 131 276 41 84 36 64 128 256), losses := [] }

theorem u15733 : Upper (D 6) (R 6) [10,129,272,33,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15734 : Route 9 := (fun mask => (mask,id))

def c15734 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15734 : Upper (D 6) (R 6) [10,129,272,33,68,64] 13 := by
  apply FastRouting.sound _ _ [10,129,272,33,68,64] 13 (by decide) (choices 1) [2,4,32] r15734 c15734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3768
  · exact u3769
  · exact u3770

def b15735 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 131 276 41 112 34 68 196 324), lower := (rows 11 131 276 41 112 34 64 128 256), losses := [] }

theorem u15735 : Upper (D 6) (R 6) [10,129,272,33,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15736 : Route 9 := (fun mask => (mask,id))

def c15736 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15736 : Upper (D 6) (R 6) [10,129,272,33,96,4] 13 := by
  apply FastRouting.sound _ _ [10,129,272,33,96,4] 13 (by decide) (choices 1) [2,4] r15736 c15736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3771
  · exact u3772

def b15737 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 276 41 112 96 70 134 262), lower := (rows 11 131 276 41 112 96 64 128 256), losses := [] }

theorem u15737 : Upper (D 6) (R 6) [10,129,272,33,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15738 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 276 44 50 33 68 196 324), lower := (rows 11 131 276 44 50 33 64 128 256), losses := [] }

theorem u15738 : Upper (D 6) (R 6) [10,129,272,36,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15739 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 276 44 50 36 65 193 321), lower := (rows 11 131 276 44 50 36 64 128 256), losses := [] }

theorem u15739 : Upper (D 6) (R 6) [10,129,272,36,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15740 : Route 9 := (fun mask => (mask,id))

def c15740 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15740 : Upper (D 6) (R 6) [10,129,272,36,34,64] 13 := by
  apply FastRouting.sound _ _ [10,129,272,36,34,64] 13 (by decide) (choices 1) [1,4] r15740 c15740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3773
  · exact u3774

def b15741 : PairBound 9 := { available := 100, camps := [], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 276 44 81 34 100 228 356), lower := (rows 11 131 276 44 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 88 152 280), good := (rows 490 162 476 492 508 34 64 128 256) },{ target := 1, region := (rows 1 0 5 8 17 32 72 136 264), good := (rows 477 149 276 492 85 32 64 128 256) }] }

theorem u15741 : Upper (D 6) (R 6) [10,129,272,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15742 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 276 44 81 36 98 226 354), lower := (rows 11 131 276 44 81 36 64 128 256), losses := [] }

theorem u15742 : Upper (D 6) (R 6) [10,129,272,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15743 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 131, targets := 64 }], pairs := [(0,6),(1,6),(3,0)], upper := (rows 11 131 276 44 81 96 102 166 294), lower := (rows 11 131 276 44 81 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 112 64 128 256), good := (rows 10 130 316 44 112 96 96 128 256) }] }

theorem u15743 : Upper (D 6) (R 6) [10,129,272,36,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15744 : PairBound 9 := { available := 100, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 276 44 82 33 100 228 356), lower := (rows 11 131 276 44 82 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 37 40 17 32 104 168 296), good := (rows 478 150 276 492 82 508 64 128 256) }] }

theorem u15744 : Upper (D 6) (R 6) [10,129,272,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15745 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 276 44 82 36 97 225 353), lower := (rows 11 131 276 44 82 36 64 128 256), losses := [] }

theorem u15745 : Upper (D 6) (R 6) [10,129,272,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15746 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 131, targets := 64 }], pairs := [(0,6),(1,6),(3,0)], upper := (rows 11 131 276 44 82 96 101 165 293), lower := (rows 11 131 276 44 82 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 112 64 128 256), good := (rows 10 130 316 44 114 96 96 128 256) }] }

theorem u15746 : Upper (D 6) (R 6) [10,129,272,36,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15747 : Route 9 := (fun mask => (mask,id))

def c15747 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15747 : Upper (D 6) (R 6) [10,129,272,36,68,1] 13 := by
  apply FastRouting.sound _ _ [10,129,272,36,68,1] 13 (by decide) (choices 1) [2,32] r15747 c15747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3775
  · exact u3776

def r15748 : Route 9 := (fun mask => (mask,id))

def c15748 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15748 : Upper (D 6) (R 6) [10,129,272,36,68,2] 13 := by
  apply FastRouting.sound _ _ [10,129,272,36,68,2] 13 (by decide) (choices 1) [1,32] r15748 c15748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3777
  · exact u3778

def b15749 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 131, targets := 4 },{ cop := 3, region := 131, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 131 276 44 84 96 99 163 291), lower := (rows 11 131 276 44 84 96 64 128 256), losses := [] }

theorem u15749 : Upper (D 6) (R 6) [10,129,272,36,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15750 : Route 9 := (fun mask => (mask,id))

def c15750 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15750 : Upper (D 6) (R 6) [10,129,272,36,96,1] 13 := by
  apply FastRouting.sound _ _ [10,129,272,36,96,1] 13 (by decide) (choices 1) [2,4] r15750 c15750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3779
  · exact u3780

def r15751 : Route 9 := (fun mask => (mask,id))

def c15751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15751 : Upper (D 6) (R 6) [10,129,272,36,96,2] 13 := by
  apply FastRouting.sound _ _ [10,129,272,36,96,2] 13 (by decide) (choices 1) [1,4] r15751 c15751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3781
  · exact u3782

def b15752 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 276 44 112 36 67 195 323), lower := (rows 11 131 276 44 112 36 64 128 256), losses := [] }

theorem u15752 : Upper (D 6) (R 6) [10,129,272,36,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15753 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 276 44 112 96 71 135 263), lower := (rows 11 131 276 44 112 96 64 128 256), losses := [] }

theorem u15753 : Upper (D 6) (R 6) [10,129,272,36,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15754 : PairBound 9 := { available := 100, camps := [], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 276 104 21 34 100 228 356), lower := (rows 11 131 276 104 21 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 42 162 476 104 508 34 64 128 256) },{ target := 1, region := (rows 1 0 37 40 19 32 104 168 296), good := (rows 477 149 276 492 21 508 64 128 256) }] }

theorem u15754 : Upper (D 6) (R 6) [10,129,272,96,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15755 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 276 104 21 36 98 226 354), lower := (rows 11 131 276 104 21 36 64 128 256), losses := [] }

theorem u15755 : Upper (D 6) (R 6) [10,129,272,96,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15756 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 276 104 21 96 102 166 294), lower := (rows 11 131 276 104 21 96 64 128 256), losses := [] }

theorem u15756 : Upper (D 6) (R 6) [10,129,272,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15757 : PairBound 9 := { available := 100, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 276 104 22 33 100 228 356), lower := (rows 11 131 276 104 22 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 37 40 19 32 104 168 296), good := (rows 478 150 276 492 22 508 64 128 256) }] }

theorem u15757 : Upper (D 6) (R 6) [10,129,272,96,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15758 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 276 104 22 36 97 225 353), lower := (rows 11 131 276 104 22 36 64 128 256), losses := [] }

theorem u15758 : Upper (D 6) (R 6) [10,129,272,96,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15759 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 276 104 22 96 101 165 293), lower := (rows 11 131 276 104 22 96 64 128 256), losses := [] }

theorem u15759 : Upper (D 6) (R 6) [10,129,272,96,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15760 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 276 104 49 34 68 196 324), lower := (rows 11 131 276 104 49 34 64 128 256), losses := [] }

theorem u15760 : Upper (D 6) (R 6) [10,129,272,96,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15761 : Route 9 := (fun mask => (mask,id))

def c15761 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15761 : Upper (D 6) (R 6) [10,129,272,96,33,4] 13 := by
  apply FastRouting.sound _ _ [10,129,272,96,33,4] 13 (by decide) (choices 1) [2,4] r15761 c15761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3783
  · exact u3784

def b15762 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 276 104 49 96 70 134 262), lower := (rows 11 131 276 104 49 96 64 128 256), losses := [] }

theorem u15762 : Upper (D 6) (R 6) [10,129,272,96,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15763 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 276 104 50 33 68 196 324), lower := (rows 11 131 276 104 50 33 64 128 256), losses := [] }

theorem u15763 : Upper (D 6) (R 6) [10,129,272,96,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15764 : Route 9 := (fun mask => (mask,id))

def c15764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15764 : Upper (D 6) (R 6) [10,129,272,96,34,4] 13 := by
  apply FastRouting.sound _ _ [10,129,272,96,34,4] 13 (by decide) (choices 1) [1,4] r15764 c15764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3785
  · exact u3786

def b15765 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 276 104 50 96 69 133 261), lower := (rows 11 131 276 104 50 96 64 128 256), losses := [] }

theorem u15765 : Upper (D 6) (R 6) [10,129,272,96,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15766 : PairBound 9 := { available := 70, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 276 104 52 33 70 198 326), lower := (rows 11 131 276 104 52 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 37 40 56 32 67 131 259), good := (rows 478 454 276 124 60 508 64 128 256) }] }

theorem u15766 : Upper (D 6) (R 6) [10,129,272,96,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15767 : PairBound 9 := { available := 69, camps := [], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 131 276 104 52 34 69 197 325), lower := (rows 11 131 276 104 52 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 37 40 56 32 67 131 259), good := (rows 477 453 276 124 60 508 64 128 256) }] }

theorem u15767 : Upper (D 6) (R 6) [10,129,272,96,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15768 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 276 104 52 36 67 195 323), lower := (rows 11 131 276 104 52 36 64 128 256), losses := [] }

theorem u15768 : Upper (D 6) (R 6) [10,129,272,96,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15769 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 276 104 52 96 71 135 263), lower := (rows 11 131 276 104 52 96 64 128 256), losses := [] }

theorem u15769 : Upper (D 6) (R 6) [10,129,272,96,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15770 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 13 84 34 112 240 368), lower := (rows 11 131 292 13 84 34 64 128 256), losses := [] }

theorem u15770 : Upper (D 6) (R 6) [10,129,288,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15771 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 131 292 13 84 48 98 226 354), lower := (rows 11 131 292 13 84 48 64 128 256), losses := [] }

theorem u15771 : Upper (D 6) (R 6) [10,129,288,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15771 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15772 : Route 9 := (fun mask => (mask,id))

def c15772 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15772 : Upper (D 6) (R 6) [10,129,288,5,68,64] 13 := by
  apply FastRouting.sound _ _ [10,129,288,5,68,64] 13 (by decide) (choices 1) [2,16,32] r15772 c15772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3787
  · exact u3788
  · exact u3789

def b15773 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 13 112 34 84 212 340), lower := (rows 11 131 292 13 112 34 64 128 256), losses := [] }

theorem u15773 : Upper (D 6) (R 6) [10,129,288,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15774 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 13 112 36 82 210 338), lower := (rows 11 131 292 13 112 36 64 128 256), losses := [] }

theorem u15774 : Upper (D 6) (R 6) [10,129,288,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15775 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 292 13 112 48 70 198 326), lower := (rows 11 131 292 13 112 48 64 128 256), losses := [] }

theorem u15775 : Upper (D 6) (R 6) [10,129,288,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15775 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15776 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 292 13 112 96 86 150 278), lower := (rows 11 131 292 13 112 96 64 128 256), losses := [] }

theorem u15776 : Upper (D 6) (R 6) [10,129,288,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15777 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 25 84 34 100 228 356), lower := (rows 11 131 292 25 84 34 64 128 256), losses := [] }

theorem u15777 : Upper (D 6) (R 6) [10,129,288,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15778 : PairBound 9 := { available := 98, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 25 84 36 98 226 354), lower := (rows 11 131 292 25 84 36 64 128 256), losses := [] }

theorem u15778 : Upper (D 6) (R 6) [10,129,288,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15779 : Route 9 := (fun mask => (mask,id))

def c15779 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15779 : Upper (D 6) (R 6) [10,129,288,17,68,64] 13 := by
  apply FastRouting.sound _ _ [10,129,288,17,68,64] 13 (by decide) (choices 1) [2,4,32] r15779 c15779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3790
  · exact u3791
  · exact u3792

#print axioms u15779
end Delivery.IrregularNine14.P06
