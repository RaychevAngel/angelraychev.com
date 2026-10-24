import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0035

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13740 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 7 98 13 168 400 33 82 210 338), lower := (rows 7 98 13 168 400 33 64 128 256), losses := [] }

theorem u13740 : Upper (D 7) (R 7) [6,96,9,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13741 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 7 98 13 168 400 34 81 209 337), lower := (rows 7 98 13 168 400 34 64 128 256), losses := [] }

theorem u13741 : Upper (D 7) (R 7) [6,96,9,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13742 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 13 168 400 48 67 195 323), lower := (rows 7 98 13 168 400 48 64 128 256), losses := [] }

theorem u13742 : Upper (D 7) (R 7) [6,96,9,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13742 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13743 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 168 400 96 83 147 275), lower := (rows 7 98 13 168 400 96 64 128 256), losses := [] }

theorem u13743 : Upper (D 7) (R 7) [6,96,9,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13744 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,1),(3,0)], upper := (rows 7 98 13 280 145 34 224 224 480), lower := (rows 7 98 13 280 145 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 21 9 17 32 98 162 290), good := (rows 477 480 29 284 157 480 64 128 256) }] }

theorem u13744 : Upper (D 7) (R 7) [6,96,9,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13745 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 280 145 96 226 162 418), lower := (rows 7 98 13 280 145 96 64 128 256), losses := [] }

theorem u13745 : Upper (D 7) (R 7) [6,96,9,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m13746_2 : Upper (D 7) (R 7) [6,96,9,272,129,128,2] 13 :=
  permutation_upper _ _ _ [6,96,9,272,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2110

theorem m13746_32 : Upper (D 7) (R 7) [6,96,9,272,129,128,32] 13 :=
  permutation_upper _ _ _ [6,96,9,272,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2111

def r13746 : Route 9 := (fun mask => (mask,id))

def c13746 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13746 : Upper (D 7) (R 7) [6,96,9,272,129,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,272,129,128] 13 (by decide) (choices 1) [2,32] r13746 c13746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m13746_2
  · exact m13746_32

def b13747 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 98 13 280 146 33 224 224 480), lower := (rows 7 98 13 280 146 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 103 167 295), good := (rows 485 480 493 280 472 481 64 128 256) }] }

theorem u13747 : Upper (D 7) (R 7) [6,96,9,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13748 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 280 146 96 225 161 417), lower := (rows 7 98 13 280 146 96 64 128 256), losses := [] }

theorem u13748 : Upper (D 7) (R 7) [6,96,9,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m13749_1 : Upper (D 7) (R 7) [6,96,9,272,130,128,1] 13 :=
  permutation_upper _ _ _ [6,96,9,272,130,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2112

theorem m13749_32 : Upper (D 7) (R 7) [6,96,9,272,130,128,32] 13 :=
  permutation_upper _ _ _ [6,96,9,272,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2113

def r13749 : Route 9 := (fun mask => (mask,id))

def c13749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13749 : Upper (D 7) (R 7) [6,96,9,272,130,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,272,130,128] 13 (by decide) (choices 1) [1,32] r13749 c13749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m13749_1
  · exact m13749_32

def r13750 : Route 9 := (fun mask => (mask,id))

def c13750 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13750 : Upper (D 7) (R 7) [6,96,9,272,160,1] 13 := by
  apply FastRouting.sound _ _ [6,96,9,272,160,1] 13 (by decide) (choices 1) [2,128] r13750 c13750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2114
  · exact u2115

def r13751 : Route 9 := (fun mask => (mask,id))

def c13751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13751 : Upper (D 7) (R 7) [6,96,9,272,160,2] 13 := by
  apply FastRouting.sound _ _ [6,96,9,272,160,2] 13 (by decide) (choices 1) [1,128] r13751 c13751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2116
  · exact u2117

def b13752 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 280 176 96 195 131 387), lower := (rows 7 98 13 280 176 96 64 128 256), losses := [] }

theorem u13752 : Upper (D 7) (R 7) [6,96,9,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13753 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 13 280 176 160 67 195 323), lower := (rows 7 98 13 280 176 160 64 128 256), losses := [] }

theorem u13753 : Upper (D 7) (R 7) [6,96,9,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13754 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 7 98 13 296 81 34 208 144 400), lower := (rows 7 98 13 296 81 34 64 128 256), losses := [] }

theorem u13754 : Upper (D 7) (R 7) [6,96,9,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13755 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 13 296 81 48 194 130 386), lower := (rows 7 98 13 296 81 48 64 128 256), losses := [] }

theorem u13755 : Upper (D 7) (R 7) [6,96,9,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13755 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13756 : Route 9 := (fun mask => (mask,id))

def c13756 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13756 : Upper (D 7) (R 7) [6,96,9,288,65,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,288,65,128] 13 (by decide) (choices 1) [2,16,128] r13756 c13756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2118
  · exact u2119
  · exact u2120

def b13757 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 7 98 13 296 145 34 208 208 464), lower := (rows 7 98 13 296 145 34 64 128 256), losses := [] }

theorem u13757 : Upper (D 7) (R 7) [6,96,9,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13758 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 7 98 13 296 145 48 194 194 450), lower := (rows 7 98 13 296 145 48 64 128 256), losses := [] }

theorem u13758 : Upper (D 7) (R 7) [6,96,9,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13758 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13759 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 296 145 96 210 146 402), lower := (rows 7 98 13 296 145 96 64 128 256), losses := [] }

theorem u13759 : Upper (D 7) (R 7) [6,96,9,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13760 : Route 9 := (fun mask => (mask,id))

def c13760 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13760 : Upper (D 7) (R 7) [6,96,9,288,129,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,288,129,128] 13 (by decide) (choices 1) [2,16] r13760 c13760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2121
  · exact u2122

def b13761 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 7 98 13 296 146 33 208 208 464), lower := (rows 7 98 13 296 146 33 64 128 256), losses := [] }

theorem u13761 : Upper (D 7) (R 7) [6,96,9,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13762 : Route 9 := (fun mask => (mask,id))

def c13762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13762 : Upper (D 7) (R 7) [6,96,9,288,130,16] 13 := by
  apply FastRouting.sound _ _ [6,96,9,288,130,16] 13 (by decide) (choices 1) [1,128] r13762 c13762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2123
  · exact u2124

def b13763 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 296 146 96 209 145 401), lower := (rows 7 98 13 296 146 96 64 128 256), losses := [] }

theorem u13763 : Upper (D 7) (R 7) [6,96,9,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13764 : Route 9 := (fun mask => (mask,id))

def c13764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13764 : Upper (D 7) (R 7) [6,96,9,288,130,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,288,130,128] 13 (by decide) (choices 1) [1,16] r13764 c13764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2125
  · exact u2126

def b13765 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 7 98 13 296 208 33 210 146 402), lower := (rows 7 98 13 296 208 33 64 128 256), losses := [] }

theorem u13765 : Upper (D 7) (R 7) [6,96,9,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13766 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 7 98 13 296 208 34 209 145 401), lower := (rows 7 98 13 296 208 34 64 128 256), losses := [] }

theorem u13766 : Upper (D 7) (R 7) [6,96,9,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13767 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 13 296 208 48 195 131 387), lower := (rows 7 98 13 296 208 48 64 128 256), losses := [] }

theorem u13767 : Upper (D 7) (R 7) [6,96,9,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13767 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13768 : Route 9 := (fun mask => (mask,id))

def c13768 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13768 : Upper (D 7) (R 7) [6,96,9,288,192,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,288,192,128] 13 (by decide) (choices 1) [1,2,16] r13768 c13768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2127
  · exact u2128
  · exact u2129

def b13769 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 98 13 392 49 34 208 208 464), lower := (rows 7 98 13 392 49 34 64 128 256), losses := [] }

theorem u13769 : Upper (D 7) (R 7) [6,96,9,384,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13770 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 7 98 13 392 49 48 194 194 450), lower := (rows 7 98 13 392 49 48 64 128 256), losses := [] }

theorem u13770 : Upper (D 7) (R 7) [6,96,9,384,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13770 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13771 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 392 49 96 210 146 402), lower := (rows 7 98 13 392 49 96 64 128 256), losses := [] }

theorem u13771 : Upper (D 7) (R 7) [6,96,9,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13772 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 458, targets := 1 },{ cop := 4, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,1)], upper := (rows 7 98 13 392 49 160 82 210 338), lower := (rows 7 98 13 392 49 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 168 64 128 256), good := (rows 21 96 61 424 49 160 64 160 256) }] }

theorem u13772 : Upper (D 7) (R 7) [6,96,9,384,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13773 : Route 9 := (fun mask => (mask,id))

def c13773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13773 : Upper (D 7) (R 7) [6,96,9,384,129,2] 13 := by
  apply FastRouting.sound _ _ [6,96,9,384,129,2] 13 (by decide) (choices 1) [16,32] r13773 c13773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2130
  · exact u2131

def b13774 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 7 98 13 392 145 48 98 226 354), lower := (rows 7 98 13 392 145 48 64 128 256), losses := [] }

theorem u13774 : Upper (D 7) (R 7) [6,96,9,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13774 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13775 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 392 145 96 114 178 306), lower := (rows 7 98 13 392 145 96 64 128 256), losses := [] }

theorem u13775 : Upper (D 7) (R 7) [6,96,9,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13776 : Route 9 := (fun mask => (mask,id))

def c13776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13776 : Upper (D 7) (R 7) [6,96,9,384,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,9,384,130,1] 13 (by decide) (choices 1) [16,32] r13776 c13776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2132
  · exact u2133

theorem m13777_1 : Upper (D 7) (R 7) [6,96,9,384,130,16,1] 13 :=
  permutation_upper _ _ _ [6,96,9,384,130,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2132

def r13777 : Route 9 := (fun mask => (mask,id))

def c13777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13777 : Upper (D 7) (R 7) [6,96,9,384,130,16] 13 := by
  apply FastRouting.sound _ _ [6,96,9,384,130,16] 13 (by decide) (choices 1) [1,32] r13777 c13777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m13777_1
  · exact u2134

def b13778 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 392 146 96 113 177 305), lower := (rows 7 98 13 392 146 96 64 128 256), losses := [] }

theorem u13778 : Upper (D 7) (R 7) [6,96,9,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13779 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 4, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 7 98 13 392 176 33 82 210 338), lower := (rows 7 98 13 392 176 33 64 128 256), losses := [] }

theorem u13779 : Upper (D 7) (R 7) [6,96,9,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13780 : Route 9 := (fun mask => (mask,id))

def c13780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13780 : Upper (D 7) (R 7) [6,96,9,384,160,2] 13 := by
  apply FastRouting.sound _ _ [6,96,9,384,160,2] 13 (by decide) (choices 1) [1,16] r13780 c13780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2135
  · exact u2136

def b13781 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 13 392 176 48 67 195 323), lower := (rows 7 98 13 392 176 48 64 128 256), losses := [] }

theorem u13781 : Upper (D 7) (R 7) [6,96,9,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13781 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13782 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 392 176 96 83 147 275), lower := (rows 7 98 13 392 176 96 64 128 256), losses := [] }

theorem u13782 : Upper (D 7) (R 7) [6,96,9,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13783 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 28 41 145 34 448 448 448), lower := (rows 7 98 28 41 145 34 64 128 256), losses := [] }

theorem u13783 : Upper (D 7) (R 7) [6,96,24,33,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13784 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 41 145 96 450 386 386), lower := (rows 7 98 28 41 145 96 64 128 256), losses := [] }

theorem u13784 : Upper (D 7) (R 7) [6,96,24,33,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13785 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 7 98 28 41 145 160 322 450 322), lower := (rows 7 98 28 41 145 160 64 128 256), losses := [] }

theorem u13785 : Upper (D 7) (R 7) [6,96,24,33,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13786 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 482, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 7 98 28 41 145 288 194 194 450), lower := (rows 7 98 28 41 145 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 25 0 67 131 259), good := (rows 471 450 28 477 465 256 64 128 256) }] }

theorem u13786 : Upper (D 7) (R 7) [6,96,24,33,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13786 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13787 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 28 41 146 33 448 448 448), lower := (rows 7 98 28 41 146 33 64 128 256), losses := [] }

theorem u13787 : Upper (D 7) (R 7) [6,96,24,33,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13788 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 41 146 96 449 385 385), lower := (rows 7 98 28 41 146 96 64 128 256), losses := [] }

theorem u13788 : Upper (D 7) (R 7) [6,96,24,33,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13789 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 0, region := 488, targets := 2 }], pairs := [(0,6),(2,6),(3,1),(3,6)], upper := (rows 7 98 28 41 146 160 321 449 321), lower := (rows 7 98 28 41 146 160 64 128 256), losses := [] }

theorem u13789 : Upper (D 7) (R 7) [6,96,24,33,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13790 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 488, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 7 98 28 41 146 288 193 193 449), lower := (rows 7 98 28 41 146 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 17 0 73 137 265), good := (rows 471 66 476 477 146 256 64 128 256) }] }

theorem u13790 : Upper (D 7) (R 7) [6,96,24,33,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13790 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13791 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 28 41 208 33 450 386 386), lower := (rows 7 98 28 41 208 33 64 128 256), losses := [] }

theorem u13791 : Upper (D 7) (R 7) [6,96,24,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13792 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 28 41 208 34 449 385 385), lower := (rows 7 98 28 41 208 34 64 128 256), losses := [] }

theorem u13792 : Upper (D 7) (R 7) [6,96,24,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13793 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 424, targets := 64 },{ cop := 3, region := 322, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(1,7),(3,6),(4,5)], upper := (rows 7 98 28 41 208 160 323 387 259), lower := (rows 7 98 28 41 208 160 64 128 256), losses := [] }

theorem u13793 : Upper (D 7) (R 7) [6,96,24,33,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13794 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 208, targets := 32 },{ cop := 0, region := 424, targets := 64 }], pairs := [(2,5),(3,6),(4,5)], upper := (rows 7 98 28 41 208 288 195 131 387), lower := (rows 7 98 28 41 208 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 25 0 65 129 257), good := (rows 471 66 28 477 208 256 64 128 256) }] }

theorem u13794 : Upper (D 7) (R 7) [6,96,24,33,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13794 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13795 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 28 41 273 34 192 192 448), lower := (rows 7 98 28 41 273 34 64 128 256), losses := [] }

theorem u13795 : Upper (D 7) (R 7) [6,96,24,33,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13796 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 41 273 96 194 130 386), lower := (rows 7 98 28 41 273 96 64 128 256), losses := [] }

theorem u13796 : Upper (D 7) (R 7) [6,96,24,33,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13797 : Route 9 := (fun mask => (mask,id))

def c13797 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13797 : Upper (D 7) (R 7) [6,96,24,33,257,128] 13 := by
  apply FastRouting.sound _ _ [6,96,24,33,257,128] 13 (by decide) (choices 1) [2,128] r13797 c13797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2137
  · exact u2138

def b13798 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 28 41 274 33 192 192 448), lower := (rows 7 98 28 41 274 33 64 128 256), losses := [] }

theorem u13798 : Upper (D 7) (R 7) [6,96,24,33,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13799 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 41 274 96 193 129 385), lower := (rows 7 98 28 41 274 96 64 128 256), losses := [] }

theorem u13799 : Upper (D 7) (R 7) [6,96,24,33,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u13799
end Delivery.IrregularNine14.P07
