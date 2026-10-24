import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0179
import IrregularNine14P07C0180

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28620 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 259 28 137 176 36 66 194 322), lower := (rows 97 259 28 137 176 36 64 128 256), losses := [] }

theorem u28620 : Upper (D 7) (R 7) [96,257,24,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28620 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28621 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 28 137 176 96 70 134 262), lower := (rows 97 259 28 137 176 96 64 128 256), losses := [] }

theorem u28621 : Upper (D 7) (R 7) [96,257,24,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28622 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,1)], upper := (rows 97 259 28 138 176 33 70 198 326), lower := (rows 97 259 28 138 176 33 64 128 256), losses := [{ target := 1, region := (rows 65 0 12 8 24 99 64 128 256), good := (rows 97 289 28 188 176 33 97 128 256) }] }

theorem u28622 : Upper (D 7) (R 7) [96,257,24,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28623 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0),(4,6)], upper := (rows 97 259 28 138 176 34 69 197 325), lower := (rows 97 259 28 138 176 34 64 128 256), losses := [] }

theorem u28623 : Upper (D 7) (R 7) [96,257,24,130,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28624 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 259 28 138 176 36 67 195 323), lower := (rows 97 259 28 138 176 36 64 128 256), losses := [] }

theorem u28624 : Upper (D 7) (R 7) [96,257,24,130,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28624 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28625 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 28 138 176 96 71 135 263), lower := (rows 97 259 28 138 176 96 64 128 256), losses := [] }

theorem u28625 : Upper (D 7) (R 7) [96,257,24,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28626 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 97 259 28 168 208 33 70 134 262), lower := (rows 97 259 28 168 208 33 64 128 256), losses := [] }

theorem u28626 : Upper (D 7) (R 7) [96,257,24,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28627_1 : Upper (D 7) (R 7) [96,257,24,160,192,2,1] 13 :=
  permutation_upper _ _ _ [96,257,24,160,192,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10797

def r28627 : Route 9 := (fun mask => (mask,id))

def c28627 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28627 : Upper (D 7) (R 7) [96,257,24,160,192,2] 13 := by
  apply FastRouting.sound _ _ [96,257,24,160,192,2] 13 (by decide) (choices 1) [1,2,4] r28627 c28627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m28627_1
  · exact u10798
  · exact u10799

def b28628 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 259 28 168 208 36 67 131 259), lower := (rows 97 259 28 168 208 36 64 128 256), losses := [] }

theorem u28628 : Upper (D 7) (R 7) [96,257,24,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28628 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28629 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 38 74 145 36 216 152 408), lower := (rows 97 259 38 74 145 36 64 128 256), losses := [] }

theorem u28629 : Upper (D 7) (R 7) [96,257,34,66,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28629 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28630 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 259 38 74 145 40 212 148 404), lower := (rows 97 259 38 74 145 40 64 128 256), losses := [] }

theorem u28630 : Upper (D 7) (R 7) [96,257,34,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28630 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28631_4 : Upper (D 7) (R 7) [96,257,34,66,129,16,4] 13 :=
  permutation_upper _ _ _ [96,257,34,66,129,8,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10802

theorem m28631_8 : Upper (D 7) (R 7) [96,257,34,66,129,16,8] 13 :=
  permutation_upper _ _ _ [96,257,34,66,129,4,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10800

def r28631 : Route 9 := (fun mask => (mask,id))

def c28631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28631 : Upper (D 7) (R 7) [96,257,34,66,129,16] 13 := by
  apply FastRouting.sound _ _ [96,257,34,66,129,16] 13 (by decide) (choices 1) [4,8,128] r28631 c28631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m28631_4
  · exact m28631_8
  · exact u10804

theorem m28632_4 : Upper (D 7) (R 7) [96,257,34,66,129,128,4] 13 :=
  permutation_upper _ _ _ [96,257,34,66,129,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10803

theorem m28632_8 : Upper (D 7) (R 7) [96,257,34,66,129,128,8] 13 :=
  permutation_upper _ _ _ [96,257,34,66,129,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10801

theorem m28632_16 : Upper (D 7) (R 7) [96,257,34,66,129,128,16] 13 :=
  permutation_upper _ _ _ [96,257,34,66,129,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10804

def r28632 : Route 9 := (fun mask => (mask,id))

def c28632 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28632 : Upper (D 7) (R 7) [96,257,34,66,129,128] 13 := by
  apply FastRouting.sound _ _ [96,257,34,66,129,128] 13 (by decide) (choices 1) [4,8,16] r28632 c28632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m28632_4
  · exact m28632_8
  · exact m28632_16

def b28633 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 259 38 74 148 33 216 152 408), lower := (rows 97 259 38 74 148 33 64 128 256), losses := [] }

theorem u28633 : Upper (D 7) (R 7) [96,257,34,66,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28634 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 259 38 74 148 40 209 145 401), lower := (rows 97 259 38 74 148 40 64 128 256), losses := [] }

theorem u28634 : Upper (D 7) (R 7) [96,257,34,66,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28634 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28635 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 394, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 38 74 148 48 201 137 393), lower := (rows 97 259 38 74 148 48 64 128 256), losses := [{ target := 5, region := (rows 1 3 4 15 20 0 67 131 259), good := (rows 459 459 478 458 156 16 64 128 256) }] }

theorem u28635 : Upper (D 7) (R 7) [96,257,34,66,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28635 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28636 : Route 9 := (fun mask => (mask,id))

def c28636 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28636 : Upper (D 7) (R 7) [96,257,34,66,132,128] 13 := by
  apply FastRouting.sound _ _ [96,257,34,66,132,128] 13 (by decide) (choices 1) [1,8,16] r28636 c28636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10805
  · exact u10806
  · exact u10807

def b28637 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 97 259 38 76 145 34 216 152 408), lower := (rows 97 259 38 76 145 34 64 128 256), losses := [] }

theorem u28637 : Upper (D 7) (R 7) [96,257,34,68,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28638 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 259 38 76 145 40 210 146 402), lower := (rows 97 259 38 76 145 40 64 128 256), losses := [] }

theorem u28638 : Upper (D 7) (R 7) [96,257,34,68,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28638 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28639 : Route 9 := (fun mask => (mask,id))

def c28639 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28639 : Upper (D 7) (R 7) [96,257,34,68,129,16] 13 := by
  apply FastRouting.sound _ _ [96,257,34,68,129,16] 13 (by decide) (choices 1) [2,8,128] r28639 c28639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10808
  · exact u10809
  · exact u10810

def r28640 : Route 9 := (fun mask => (mask,id))

def c28640 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28640 : Upper (D 7) (R 7) [96,257,34,68,129,128] 13 := by
  apply FastRouting.sound _ _ [96,257,34,68,129,128] 13 (by decide) (choices 1) [2,8,16] r28640 c28640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10811
  · exact u10812
  · exact u10813

def b28641 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 259 38 76 146 33 216 152 408), lower := (rows 97 259 38 76 146 33 64 128 256), losses := [] }

theorem u28641 : Upper (D 7) (R 7) [96,257,34,68,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28642 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 259 38 76 146 40 209 145 401), lower := (rows 97 259 38 76 146 40 64 128 256), losses := [] }

theorem u28642 : Upper (D 7) (R 7) [96,257,34,68,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28642 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28643 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 36, targets := 193 }], pairs := [(2,0),(2,6),(2,7)], upper := (rows 97 259 38 76 146 48 201 137 393), lower := (rows 97 259 38 76 146 48 64 128 256), losses := [] }

theorem u28643 : Upper (D 7) (R 7) [96,257,34,68,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28643 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28644 : Route 9 := (fun mask => (mask,id))

def c28644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28644 : Upper (D 7) (R 7) [96,257,34,68,130,128] 13 := by
  apply FastRouting.sound _ _ [96,257,34,68,130,128] 13 (by decide) (choices 1) [1,8,16] r28644 c28644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10814
  · exact u10815
  · exact u10816

def b28645 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 259 38 76 152 33 210 146 402), lower := (rows 97 259 38 76 152 33 64 128 256), losses := [] }

theorem u28645 : Upper (D 7) (R 7) [96,257,34,68,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28646 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 97 259 38 76 152 34 209 145 401), lower := (rows 97 259 38 76 152 34 64 128 256), losses := [] }

theorem u28646 : Upper (D 7) (R 7) [96,257,34,68,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28647 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5),(1,6),(2,6)], upper := (rows 97 259 38 76 152 48 195 131 387), lower := (rows 97 259 38 76 152 48 64 128 256), losses := [] }

theorem u28647 : Upper (D 7) (R 7) [96,257,34,68,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28647 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28648 : Route 9 := (fun mask => (mask,id))

def c28648 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28648 : Upper (D 7) (R 7) [96,257,34,68,136,128] 13 := by
  apply FastRouting.sound _ _ [96,257,34,68,136,128] 13 (by decide) (choices 1) [1,2,16] r28648 c28648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10817
  · exact u10818
  · exact u10819

def b28649 : PairBound 9 := { available := 140, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 97 259 38 88 145 34 204 140 396), lower := (rows 97 259 38 88 145 34 64 128 256), losses := [] }

theorem u28649 : Upper (D 7) (R 7) [96,257,34,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28650 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 38 88 145 36 202 138 394), lower := (rows 97 259 38 88 145 36 64 128 256), losses := [] }

theorem u28650 : Upper (D 7) (R 7) [96,257,34,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28650 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28651 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 259 38 88 145 40 198 134 390), lower := (rows 97 259 38 88 145 40 64 128 256), losses := [] }

theorem u28651 : Upper (D 7) (R 7) [96,257,34,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28651 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28652 : Route 9 := (fun mask => (mask,id))

def c28652 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28652 : Upper (D 7) (R 7) [96,257,34,80,129,128] 13 := by
  apply FastRouting.sound _ _ [96,257,34,80,129,128] 13 (by decide) (choices 1) [2,4,8] r28652 c28652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10820
  · exact u10821
  · exact u10822

def b28653 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 259 38 88 146 33 204 140 396), lower := (rows 97 259 38 88 146 33 64 128 256), losses := [] }

theorem u28653 : Upper (D 7) (R 7) [96,257,34,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28654 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 38 88 146 36 201 137 393), lower := (rows 97 259 38 88 146 36 64 128 256), losses := [] }

theorem u28654 : Upper (D 7) (R 7) [96,257,34,80,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28654 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28655 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 259 38 88 146 40 197 133 389), lower := (rows 97 259 38 88 146 40 64 128 256), losses := [] }

theorem u28655 : Upper (D 7) (R 7) [96,257,34,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28655 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28656 : Route 9 := (fun mask => (mask,id))

def c28656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28656 : Upper (D 7) (R 7) [96,257,34,80,130,128] 13 := by
  apply FastRouting.sound _ _ [96,257,34,80,130,128] 13 (by decide) (choices 1) [1,4,8] r28656 c28656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10823
  · exact u10824
  · exact u10825

def b28657 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 259 38 88 148 33 202 138 394), lower := (rows 97 259 38 88 148 33 64 128 256), losses := [] }

theorem u28657 : Upper (D 7) (R 7) [96,257,34,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28658 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 97 259 38 88 148 34 201 137 393), lower := (rows 97 259 38 88 148 34 64 128 256), losses := [] }

theorem u28658 : Upper (D 7) (R 7) [96,257,34,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28659 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 259 38 88 148 40 195 131 387), lower := (rows 97 259 38 88 148 40 64 128 256), losses := [] }

theorem u28659 : Upper (D 7) (R 7) [96,257,34,80,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28659 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28660 : Route 9 := (fun mask => (mask,id))

def c28660 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28660 : Upper (D 7) (R 7) [96,257,34,80,132,128] 13 := by
  apply FastRouting.sound _ _ [96,257,34,80,132,128] 13 (by decide) (choices 1) [1,2,8] r28660 c28660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10826
  · exact u10827
  · exact u10828

def b28661 : PairBound 9 := { available := 134, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 259 38 88 152 33 198 134 390), lower := (rows 97 259 38 88 152 33 64 128 256), losses := [] }

theorem u28661 : Upper (D 7) (R 7) [96,257,34,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28662 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 217, targets := 2 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 97 259 38 88 152 34 197 133 389), lower := (rows 97 259 38 88 152 34 64 128 256), losses := [] }

theorem u28662 : Upper (D 7) (R 7) [96,257,34,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28663 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 38 88 152 36 195 131 387), lower := (rows 97 259 38 88 152 36 64 128 256), losses := [] }

theorem u28663 : Upper (D 7) (R 7) [96,257,34,80,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28663 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28664 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 262, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(2,7)], upper := (rows 97 259 38 88 152 160 71 135 263), lower := (rows 97 259 38 88 152 160 64 128 256), losses := [] }

theorem u28664 : Upper (D 7) (R 7) [96,257,34,80,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28665 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 38 137 146 36 88 216 344), lower := (rows 97 259 38 137 146 36 64 128 256), losses := [] }

theorem u28665 : Upper (D 7) (R 7) [96,257,34,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28665 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28666 : Route 9 := (fun mask => (mask,id))

def c28666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28666 : Upper (D 7) (R 7) [96,257,34,129,130,8] 13 := by
  apply FastRouting.sound _ _ [96,257,34,129,130,8] 13 (by decide) (choices 1) [4,16] r28666 c28666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10829
  · exact u10830

def b28667 : PairBound 9 := { available := 76, camps := [{ cop := 4, region := 36, targets := 193 }], pairs := [(2,0),(2,6),(2,7)], upper := (rows 97 259 38 137 146 48 76 204 332), lower := (rows 97 259 38 137 146 48 64 128 256), losses := [] }

theorem u28667 : Upper (D 7) (R 7) [96,257,34,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28667 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28668 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 38 137 146 96 92 156 284), lower := (rows 97 259 38 137 146 96 64 128 256), losses := [] }

theorem u28668 : Upper (D 7) (R 7) [96,257,34,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28669 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 97 259 38 137 148 34 88 216 344), lower := (rows 97 259 38 137 148 34 64 128 256), losses := [] }

theorem u28669 : Upper (D 7) (R 7) [96,257,34,129,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28670 : Route 9 := (fun mask => (mask,id))

def c28670 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28670 : Upper (D 7) (R 7) [96,257,34,129,132,8] 13 := by
  apply FastRouting.sound _ _ [96,257,34,129,132,8] 13 (by decide) (choices 1) [2,16] r28670 c28670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10831
  · exact u10832

def b28671 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 394, targets := 32 },{ cop := 3, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(3,5)], upper := (rows 97 259 38 137 148 48 74 202 330), lower := (rows 97 259 38 137 148 48 64 128 256), losses := [] }

theorem u28671 : Upper (D 7) (R 7) [96,257,34,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28671 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28672 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 38 137 148 96 90 154 282), lower := (rows 97 259 38 137 148 96 64 128 256), losses := [] }

theorem u28672 : Upper (D 7) (R 7) [96,257,34,129,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28673 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 97 259 38 137 208 34 92 156 284), lower := (rows 97 259 38 137 208 34 64 128 256), losses := [] }

theorem u28673 : Upper (D 7) (R 7) [96,257,34,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28674 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 38 137 208 36 90 154 282), lower := (rows 97 259 38 137 208 36 64 128 256), losses := [] }

theorem u28674 : Upper (D 7) (R 7) [96,257,34,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28674 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28675 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 208, targets := 33 },{ cop := 4, region := 41, targets := 2 }], pairs := [(0,1),(4,0),(4,5)], upper := (rows 97 259 38 137 208 40 86 150 278), lower := (rows 97 259 38 137 208 40 64 128 256), losses := [] }

theorem u28675 : Upper (D 7) (R 7) [96,257,34,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28675 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28676 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 38 137 208 48 78 142 270), lower := (rows 97 259 38 137 208 48 64 128 256), losses := [] }

theorem u28676 : Upper (D 7) (R 7) [96,257,34,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28676 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28677 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 259 38 138 148 33 88 216 344), lower := (rows 97 259 38 138 148 33 64 128 256), losses := [] }

theorem u28677 : Upper (D 7) (R 7) [96,257,34,130,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28678 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 97 259 38 138 148 40 81 209 337), lower := (rows 97 259 38 138 148 40 64 128 256), losses := [] }

theorem u28678 : Upper (D 7) (R 7) [96,257,34,130,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28678 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28679 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 97 259 38 138 148 48 73 201 329), lower := (rows 97 259 38 138 148 48 64 128 256), losses := [] }

theorem u28679 : Upper (D 7) (R 7) [96,257,34,130,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28679 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u28679
end Delivery.IrregularNine14.P07
