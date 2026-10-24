import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0646
import IrregularNine14P06C0647
import IrregularNine14P06C0648
import IrregularNine14P06C0649
import IrregularNine14P06C0650

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m43200_6 : Upper (D 6) (R 6) [34,192,257,65,6] 13 :=
  permutation_upper _ _ _ [34,192,257,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38785

theorem m43200_10 : Upper (D 6) (R 6) [34,192,257,65,10] 13 :=
  permutation_upper _ _ _ [34,192,257,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38802

theorem m43200_12 : Upper (D 6) (R 6) [34,192,257,65,12] 13 :=
  permutation_upper _ _ _ [34,192,257,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38811

theorem m43200_34 : Upper (D 6) (R 6) [34,192,257,65,34] 13 :=
  permutation_upper _ _ _ [34,192,257,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38818

theorem m43200_36 : Upper (D 6) (R 6) [34,192,257,65,36] 13 :=
  permutation_upper _ _ _ [34,192,257,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38821

theorem m43200_40 : Upper (D 6) (R 6) [34,192,257,65,40] 13 :=
  permutation_upper _ _ _ [34,192,257,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38825

def r43200 : Route 9 := (fun mask => (mask,id))

def c43200 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43200 : Upper (D 6) (R 6) [34,192,257,65] 13 := by
  apply FastRouting.sound _ _ [34,192,257,65] 13 (by decide) (choices 2) [6,10,12,34,36,40] r43200 c43200
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43200_6
  · exact m43200_10
  · exact m43200_12
  · exact m43200_34
  · exact m43200_36
  · exact m43200_40

def b43201 : PairBound 9 := { available := 61, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 194 261 74 61 61 125 189 317), lower := (rows 35 194 261 74 16 32 64 128 256), losses := [] }

theorem u43201 : Upper (D 6) (R 6) [34,192,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43202_3 : Upper (D 6) (R 6) [34,192,257,68,3] 13 :=
  permutation_upper _ _ _ [34,192,257,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38769

theorem m43202_5 : Upper (D 6) (R 6) [34,192,257,68,5] 13 :=
  permutation_upper _ _ _ [34,192,257,5,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38777

theorem m43202_6 : Upper (D 6) (R 6) [34,192,257,68,6] 13 :=
  permutation_upper _ _ _ [34,192,257,6,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38786

theorem m43202_9 : Upper (D 6) (R 6) [34,192,257,68,9] 13 :=
  permutation_upper _ _ _ [34,192,257,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38795

theorem m43202_10 : Upper (D 6) (R 6) [34,192,257,68,10] 13 :=
  permutation_upper _ _ _ [34,192,257,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38803

theorem m43202_12 : Upper (D 6) (R 6) [34,192,257,68,12] 13 :=
  permutation_upper _ _ _ [34,192,257,20,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38813

theorem m43202_33 : Upper (D 6) (R 6) [34,192,257,68,33] 13 :=
  permutation_upper _ _ _ [34,192,257,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38816

theorem m43202_34 : Upper (D 6) (R 6) [34,192,257,68,34] 13 :=
  permutation_upper _ _ _ [34,192,257,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38819

theorem m43202_36 : Upper (D 6) (R 6) [34,192,257,68,36] 13 :=
  permutation_upper _ _ _ [34,192,257,36,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38823

theorem m43202_40 : Upper (D 6) (R 6) [34,192,257,68,40] 13 :=
  permutation_upper _ _ _ [34,192,257,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38827

def r43202 : Route 9 := (fun mask => (mask,id))

def c43202 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43202 : Upper (D 6) (R 6) [34,192,257,68] 13 := by
  apply FastRouting.sound _ _ [34,192,257,68] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r43202 c43202
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43202_3
  · exact m43202_5
  · exact m43202_6
  · exact m43202_9
  · exact m43202_10
  · exact m43202_12
  · exact m43202_33
  · exact m43202_34
  · exact m43202_36
  · exact m43202_40

theorem m43203_3 : Upper (D 6) (R 6) [34,192,257,80,3] 13 :=
  permutation_upper _ _ _ [34,192,257,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38770

theorem m43203_5 : Upper (D 6) (R 6) [34,192,257,80,5] 13 :=
  permutation_upper _ _ _ [34,192,257,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38778

theorem m43203_6 : Upper (D 6) (R 6) [34,192,257,80,6] 13 :=
  permutation_upper _ _ _ [34,192,257,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38787

theorem m43203_9 : Upper (D 6) (R 6) [34,192,257,80,9] 13 :=
  permutation_upper _ _ _ [34,192,257,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38796

theorem m43203_10 : Upper (D 6) (R 6) [34,192,257,80,10] 13 :=
  permutation_upper _ _ _ [34,192,257,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38804

theorem m43203_12 : Upper (D 6) (R 6) [34,192,257,80,12] 13 :=
  permutation_upper _ _ _ [34,192,257,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38814

theorem m43203_33 : Upper (D 6) (R 6) [34,192,257,80,33] 13 :=
  permutation_upper _ _ _ [34,192,257,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38817

theorem m43203_34 : Upper (D 6) (R 6) [34,192,257,80,34] 13 :=
  permutation_upper _ _ _ [34,192,257,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38820

theorem m43203_36 : Upper (D 6) (R 6) [34,192,257,80,36] 13 :=
  permutation_upper _ _ _ [34,192,257,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38824

theorem m43203_40 : Upper (D 6) (R 6) [34,192,257,80,40] 13 :=
  permutation_upper _ _ _ [34,192,257,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38828

def r43203 : Route 9 := (fun mask => (mask,id))

def c43203 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43203 : Upper (D 6) (R 6) [34,192,257,80] 13 := by
  apply FastRouting.sound _ _ [34,192,257,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r43203 c43203
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43203_3
  · exact m43203_5
  · exact m43203_6
  · exact m43203_9
  · exact m43203_10
  · exact m43203_12
  · exact m43203_33
  · exact m43203_34
  · exact m43203_36
  · exact m43203_40

theorem m43204_3 : Upper (D 6) (R 6) [34,192,257,96,3] 13 :=
  permutation_upper _ _ _ [34,192,257,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38771

theorem m43204_5 : Upper (D 6) (R 6) [34,192,257,96,5] 13 :=
  permutation_upper _ _ _ [34,192,257,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38779

theorem m43204_6 : Upper (D 6) (R 6) [34,192,257,96,6] 13 :=
  permutation_upper _ _ _ [34,192,257,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38788

theorem m43204_9 : Upper (D 6) (R 6) [34,192,257,96,9] 13 :=
  permutation_upper _ _ _ [34,192,257,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38797

theorem m43204_10 : Upper (D 6) (R 6) [34,192,257,96,10] 13 :=
  permutation_upper _ _ _ [34,192,257,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38805

theorem m43204_12 : Upper (D 6) (R 6) [34,192,257,96,12] 13 :=
  permutation_upper _ _ _ [34,192,257,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38815

def r43204 : Route 9 := (fun mask => (mask,id))

def c43204 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43204 : Upper (D 6) (R 6) [34,192,257,96] 13 := by
  apply FastRouting.sound _ _ [34,192,257,96] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43204 c43204
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43204_3
  · exact m43204_5
  · exact m43204_6
  · exact m43204_9
  · exact m43204_10
  · exact m43204_12

def r43205 : Route 9 := (fun mask => (mask,id))

def c43205 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43205 : Upper (D 6) (R 6) [34,192,258,5] 13 := by
  apply FastRouting.sound _ _ [34,192,258,5] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r43205 c43205
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38829
  · exact u38830
  · exact u38831
  · exact u38832
  · exact u38833
  · exact u38834
  · exact u38835
  · exact u38836
  · exact u38837
  · exact u38838

theorem m43206_5 : Upper (D 6) (R 6) [34,192,258,17,5] 13 :=
  permutation_upper _ _ _ [34,192,258,5,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38830

def r43206 : Route 9 := (fun mask => (mask,id))

def c43206 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43206 : Upper (D 6) (R 6) [34,192,258,17] 13 := by
  apply FastRouting.sound _ _ [34,192,258,17] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r43206 c43206
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43206_5
  · exact u38839
  · exact u38840
  · exact u38841
  · exact u38842
  · exact u38843
  · exact u38844
  · exact u38845
  · exact u38846
  · exact u38847

theorem m43207_5 : Upper (D 6) (R 6) [34,192,258,20,5] 13 :=
  permutation_upper _ _ _ [34,192,258,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38831

theorem m43207_9 : Upper (D 6) (R 6) [34,192,258,20,9] 13 :=
  permutation_upper _ _ _ [34,192,258,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38840

def r43207 : Route 9 := (fun mask => (mask,id))

def c43207 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43207 : Upper (D 6) (R 6) [34,192,258,20] 13 := by
  apply FastRouting.sound _ _ [34,192,258,20] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r43207 c43207
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43207_5
  · exact m43207_9
  · exact u38848
  · exact u38849
  · exact u38850
  · exact u38851
  · exact u38852
  · exact u38853
  · exact u38854
  · exact u38855

def b43208 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 262 41 93 125 93 221 349), lower := (rows 35 194 262 41 16 32 64 128 256), losses := [] }

theorem u43208 : Upper (D 6) (R 6) [34,192,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43209_5 : Upper (D 6) (R 6) [34,192,258,36,5] 13 :=
  permutation_upper _ _ _ [34,192,258,5,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38833

theorem m43209_9 : Upper (D 6) (R 6) [34,192,258,36,9] 13 :=
  permutation_upper _ _ _ [34,192,258,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38842

theorem m43209_12 : Upper (D 6) (R 6) [34,192,258,36,12] 13 :=
  permutation_upper _ _ _ [34,192,258,20,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38850

def r43209 : Route 9 := (fun mask => (mask,id))

def c43209 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43209 : Upper (D 6) (R 6) [34,192,258,36] 13 := by
  apply FastRouting.sound _ _ [34,192,258,36] 13 (by decide) (choices 2) [5,9,12,65,68,72] r43209 c43209
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43209_5
  · exact m43209_9
  · exact m43209_12
  · exact u38859
  · exact u38860
  · exact u38861

theorem m43210_5 : Upper (D 6) (R 6) [34,192,258,48,5] 13 :=
  permutation_upper _ _ _ [34,192,258,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38834

theorem m43210_9 : Upper (D 6) (R 6) [34,192,258,48,9] 13 :=
  permutation_upper _ _ _ [34,192,258,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38843

theorem m43210_12 : Upper (D 6) (R 6) [34,192,258,48,12] 13 :=
  permutation_upper _ _ _ [34,192,258,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38851

def r43210 : Route 9 := (fun mask => (mask,id))

def c43210 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43210 : Upper (D 6) (R 6) [34,192,258,48] 13 := by
  apply FastRouting.sound _ _ [34,192,258,48] 13 (by decide) (choices 2) [5,9,12,65,68,72] r43210 c43210
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43210_5
  · exact m43210_9
  · exact m43210_12
  · exact u38862
  · exact u38863
  · exact u38864

theorem m43211_5 : Upper (D 6) (R 6) [34,192,258,65,5] 13 :=
  permutation_upper _ _ _ [34,192,258,5,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38835

theorem m43211_9 : Upper (D 6) (R 6) [34,192,258,65,9] 13 :=
  permutation_upper _ _ _ [34,192,258,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38844

theorem m43211_12 : Upper (D 6) (R 6) [34,192,258,65,12] 13 :=
  permutation_upper _ _ _ [34,192,258,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38852

theorem m43211_33 : Upper (D 6) (R 6) [34,192,258,65,33] 13 :=
  permutation_upper _ _ _ [34,192,258,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38856

theorem m43211_36 : Upper (D 6) (R 6) [34,192,258,65,36] 13 :=
  permutation_upper _ _ _ [34,192,258,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38859

theorem m43211_40 : Upper (D 6) (R 6) [34,192,258,65,40] 13 :=
  permutation_upper _ _ _ [34,192,258,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38862

def r43211 : Route 9 := (fun mask => (mask,id))

def c43211 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43211 : Upper (D 6) (R 6) [34,192,258,65] 13 := by
  apply FastRouting.sound _ _ [34,192,258,65] 13 (by decide) (choices 2) [5,9,12,33,36,40] r43211 c43211
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43211_5
  · exact m43211_9
  · exact m43211_12
  · exact m43211_33
  · exact m43211_36
  · exact m43211_40

theorem m43212_5 : Upper (D 6) (R 6) [34,192,258,68,5] 13 :=
  permutation_upper _ _ _ [34,192,258,5,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38836

theorem m43212_9 : Upper (D 6) (R 6) [34,192,258,68,9] 13 :=
  permutation_upper _ _ _ [34,192,258,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38845

theorem m43212_12 : Upper (D 6) (R 6) [34,192,258,68,12] 13 :=
  permutation_upper _ _ _ [34,192,258,20,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38853

theorem m43212_33 : Upper (D 6) (R 6) [34,192,258,68,33] 13 :=
  permutation_upper _ _ _ [34,192,258,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38857

theorem m43212_36 : Upper (D 6) (R 6) [34,192,258,68,36] 13 :=
  permutation_upper _ _ _ [34,192,258,36,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38860

theorem m43212_40 : Upper (D 6) (R 6) [34,192,258,68,40] 13 :=
  permutation_upper _ _ _ [34,192,258,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38863

def r43212 : Route 9 := (fun mask => (mask,id))

def c43212 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43212 : Upper (D 6) (R 6) [34,192,258,68] 13 := by
  apply FastRouting.sound _ _ [34,192,258,68] 13 (by decide) (choices 2) [5,9,12,33,36,40] r43212 c43212
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43212_5
  · exact m43212_9
  · exact m43212_12
  · exact m43212_33
  · exact m43212_36
  · exact m43212_40

theorem m43213_5 : Upper (D 6) (R 6) [34,192,258,80,5] 13 :=
  permutation_upper _ _ _ [34,192,258,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38837

theorem m43213_9 : Upper (D 6) (R 6) [34,192,258,80,9] 13 :=
  permutation_upper _ _ _ [34,192,258,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38846

theorem m43213_12 : Upper (D 6) (R 6) [34,192,258,80,12] 13 :=
  permutation_upper _ _ _ [34,192,258,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38854

theorem m43213_33 : Upper (D 6) (R 6) [34,192,258,80,33] 13 :=
  permutation_upper _ _ _ [34,192,258,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38858

theorem m43213_36 : Upper (D 6) (R 6) [34,192,258,80,36] 13 :=
  permutation_upper _ _ _ [34,192,258,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38861

theorem m43213_40 : Upper (D 6) (R 6) [34,192,258,80,40] 13 :=
  permutation_upper _ _ _ [34,192,258,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38864

def r43213 : Route 9 := (fun mask => (mask,id))

def c43213 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43213 : Upper (D 6) (R 6) [34,192,258,80] 13 := by
  apply FastRouting.sound _ _ [34,192,258,80] 13 (by decide) (choices 2) [5,9,12,33,36,40] r43213 c43213
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43213_5
  · exact m43213_9
  · exact m43213_12
  · exact m43213_33
  · exact m43213_36
  · exact m43213_40

theorem m43214_5 : Upper (D 6) (R 6) [34,192,258,96,5] 13 :=
  permutation_upper _ _ _ [34,192,258,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38838

theorem m43214_9 : Upper (D 6) (R 6) [34,192,258,96,9] 13 :=
  permutation_upper _ _ _ [34,192,258,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38847

theorem m43214_12 : Upper (D 6) (R 6) [34,192,258,96,12] 13 :=
  permutation_upper _ _ _ [34,192,258,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38855

def r43214 : Route 9 := (fun mask => (mask,id))

def c43214 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43214 : Upper (D 6) (R 6) [34,192,258,96] 13 := by
  apply FastRouting.sound _ _ [34,192,258,96] 13 (by decide) (choices 2) [5,9,12] r43214 c43214
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m43214_5
  · exact m43214_9
  · exact m43214_12

def b43215 : PairBound 9 := { available := 117, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 268 11 117 117 117 245 373), lower := (rows 35 194 268 11 16 32 64 128 256), losses := [] }

theorem u43215 : Upper (D 6) (R 6) [34,192,264,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43216 : Route 9 := (fun mask => (mask,id))

def c43216 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43216 : Upper (D 6) (R 6) [34,192,264,5] 13 := by
  apply FastRouting.sound _ _ [34,192,264,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43216 c43216
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38865
  · exact u38866
  · exact u38867
  · exact u38868
  · exact u38869
  · exact u38870
  · exact u38871
  · exact u38872
  · exact u38873
  · exact u38874

def r43217 : Route 9 := (fun mask => (mask,id))

def c43217 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43217 : Upper (D 6) (R 6) [34,192,264,6] 13 := by
  apply FastRouting.sound _ _ [34,192,264,6] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43217 c43217
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38875
  · exact u38876
  · exact u38877
  · exact u38878
  · exact u38879
  · exact u38880

def r43218 : Route 9 := (fun mask => (mask,id))

def c43218 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43218 : Upper (D 6) (R 6) [34,192,264,17] 13 := by
  apply FastRouting.sound _ _ [34,192,264,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43218 c43218
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38881
  · exact u38882
  · exact u38883
  · exact u38884
  · exact u38885
  · exact u38886
  · exact u38887
  · exact u38888
  · exact u38889
  · exact u38890

def r43219 : Route 9 := (fun mask => (mask,id))

def c43219 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43219 : Upper (D 6) (R 6) [34,192,264,18] 13 := by
  apply FastRouting.sound _ _ [34,192,264,18] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43219 c43219
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38891
  · exact u38892
  · exact u38893
  · exact u38894
  · exact u38895
  · exact u38896

def r43220 : Route 9 := (fun mask => (mask,id))

def c43220 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43220 : Upper (D 6) (R 6) [34,192,264,20] 13 := by
  apply FastRouting.sound _ _ [34,192,264,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43220 c43220
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38897
  · exact u38898
  · exact u38899
  · exact u38900
  · exact u38901
  · exact u38902
  · exact u38903
  · exact u38904
  · exact u38905
  · exact u38906

def b43221 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 268 41 87 119 87 215 343), lower := (rows 35 194 268 41 16 32 64 128 256), losses := [] }

theorem u43221 : Upper (D 6) (R 6) [34,192,264,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43222 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 194 268 42 85 117 85 213 341), lower := (rows 35 194 268 42 16 32 64 128 256), losses := [] }

theorem u43222 : Upper (D 6) (R 6) [34,192,264,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43223 : Route 9 := (fun mask => (mask,id))

def c43223 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43223 : Upper (D 6) (R 6) [34,192,264,36] 13 := by
  apply FastRouting.sound _ _ [34,192,264,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43223 c43223
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38907
  · exact u38908
  · exact u38909
  · exact u38910
  · exact u38911
  · exact u38912

def r43224 : Route 9 := (fun mask => (mask,id))

def c43224 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43224 : Upper (D 6) (R 6) [34,192,264,48] 13 := by
  apply FastRouting.sound _ _ [34,192,264,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43224 c43224
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38913
  · exact u38914
  · exact u38915
  · exact u38916
  · exact u38917
  · exact u38918

def r43225 : Route 9 := (fun mask => (mask,id))

def c43225 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43225 : Upper (D 6) (R 6) [34,192,264,65] 13 := by
  apply FastRouting.sound _ _ [34,192,264,65] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43225 c43225
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38919
  · exact u38920
  · exact u38921
  · exact u38922
  · exact u38923
  · exact u38924

def b43226 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 194 268 74 53 53 117 181 309), lower := (rows 35 194 268 74 16 32 64 128 256), losses := [] }

theorem u43226 : Upper (D 6) (R 6) [34,192,264,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43227 : Route 9 := (fun mask => (mask,id))

def c43227 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43227 : Upper (D 6) (R 6) [34,192,264,68] 13 := by
  apply FastRouting.sound _ _ [34,192,264,68] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43227 c43227
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38925
  · exact u38926
  · exact u38927
  · exact u38928
  · exact u38929
  · exact u38930

def r43228 : Route 9 := (fun mask => (mask,id))

def c43228 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43228 : Upper (D 6) (R 6) [34,192,264,80] 13 := by
  apply FastRouting.sound _ _ [34,192,264,80] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43228 c43228
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38931
  · exact u38932
  · exact u38933
  · exact u38934
  · exact u38935
  · exact u38936

def r43229 : Route 9 := (fun mask => (mask,id))

def c43229 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43229 : Upper (D 6) (R 6) [34,192,264,96] 13 := by
  apply FastRouting.sound _ _ [34,192,264,96] 13 (by decide) (choices 2) [3,5,6] r43229 c43229
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38937
  · exact u38938
  · exact u38939

def b43230 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 292 11 93 125 93 221 349), lower := (rows 35 194 292 11 16 32 64 128 256), losses := [] }

theorem u43230 : Upper (D 6) (R 6) [34,192,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43231_3 : Upper (D 6) (R 6) [34,192,288,5,3] 13 :=
  permutation_upper _ _ _ [34,192,288,3,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38940

def r43231 : Route 9 := (fun mask => (mask,id))

def c43231 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43231 : Upper (D 6) (R 6) [34,192,288,5] 13 := by
  apply FastRouting.sound _ _ [34,192,288,5] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43231 c43231
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43231_3
  · exact u38946
  · exact u38947
  · exact u38948
  · exact u38949
  · exact u38950
  · exact u38951
  · exact u38952
  · exact u38953
  · exact u38954

theorem m43232_5 : Upper (D 6) (R 6) [34,192,288,6,5] 13 :=
  permutation_upper _ _ _ [34,192,288,5,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38947

def r43232 : Route 9 := (fun mask => (mask,id))

def c43232 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43232 : Upper (D 6) (R 6) [34,192,288,6] 13 := by
  apply FastRouting.sound _ _ [34,192,288,6] 13 (by decide) (choices 2) [5,9,12,65,68,72] r43232 c43232
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43232_5
  · exact u38955
  · exact u38956
  · exact u38957
  · exact u38958
  · exact u38959

theorem m43233_3 : Upper (D 6) (R 6) [34,192,288,17,3] 13 :=
  permutation_upper _ _ _ [34,192,288,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38941

theorem m43233_5 : Upper (D 6) (R 6) [34,192,288,17,5] 13 :=
  permutation_upper _ _ _ [34,192,288,5,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38948

theorem m43233_6 : Upper (D 6) (R 6) [34,192,288,17,6] 13 :=
  permutation_upper _ _ _ [34,192,288,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38955

def r43233 : Route 9 := (fun mask => (mask,id))

def c43233 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43233 : Upper (D 6) (R 6) [34,192,288,17] 13 := by
  apply FastRouting.sound _ _ [34,192,288,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43233 c43233
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43233_3
  · exact m43233_5
  · exact m43233_6
  · exact u38960
  · exact u38961
  · exact u38962
  · exact u38963
  · exact u38964
  · exact u38965
  · exact u38966

theorem m43234_5 : Upper (D 6) (R 6) [34,192,288,18,5] 13 :=
  permutation_upper _ _ _ [34,192,288,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38949

theorem m43234_9 : Upper (D 6) (R 6) [34,192,288,18,9] 13 :=
  permutation_upper _ _ _ [34,192,288,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38961

def r43234 : Route 9 := (fun mask => (mask,id))

def c43234 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43234 : Upper (D 6) (R 6) [34,192,288,18] 13 := by
  apply FastRouting.sound _ _ [34,192,288,18] 13 (by decide) (choices 2) [5,9,12,65,68,72] r43234 c43234
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43234_5
  · exact m43234_9
  · exact u38967
  · exact u38968
  · exact u38969
  · exact u38970

theorem m43235_3 : Upper (D 6) (R 6) [34,192,288,20,3] 13 :=
  permutation_upper _ _ _ [34,192,288,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38942

theorem m43235_5 : Upper (D 6) (R 6) [34,192,288,20,5] 13 :=
  permutation_upper _ _ _ [34,192,288,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38950

theorem m43235_6 : Upper (D 6) (R 6) [34,192,288,20,6] 13 :=
  permutation_upper _ _ _ [34,192,288,6,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38956

theorem m43235_9 : Upper (D 6) (R 6) [34,192,288,20,9] 13 :=
  permutation_upper _ _ _ [34,192,288,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38962

theorem m43235_10 : Upper (D 6) (R 6) [34,192,288,20,10] 13 :=
  permutation_upper _ _ _ [34,192,288,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38967

def r43235 : Route 9 := (fun mask => (mask,id))

def c43235 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43235 : Upper (D 6) (R 6) [34,192,288,20] 13 := by
  apply FastRouting.sound _ _ [34,192,288,20] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43235 c43235
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43235_3
  · exact m43235_5
  · exact m43235_6
  · exact m43235_9
  · exact m43235_10
  · exact u38971
  · exact u38972
  · exact u38973
  · exact u38974
  · exact u38975

theorem m43236_3 : Upper (D 6) (R 6) [34,192,288,65,3] 13 :=
  permutation_upper _ _ _ [34,192,288,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38943

theorem m43236_5 : Upper (D 6) (R 6) [34,192,288,65,5] 13 :=
  permutation_upper _ _ _ [34,192,288,5,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38951

theorem m43236_6 : Upper (D 6) (R 6) [34,192,288,65,6] 13 :=
  permutation_upper _ _ _ [34,192,288,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38957

theorem m43236_9 : Upper (D 6) (R 6) [34,192,288,65,9] 13 :=
  permutation_upper _ _ _ [34,192,288,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38963

theorem m43236_10 : Upper (D 6) (R 6) [34,192,288,65,10] 13 :=
  permutation_upper _ _ _ [34,192,288,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38968

theorem m43236_12 : Upper (D 6) (R 6) [34,192,288,65,12] 13 :=
  permutation_upper _ _ _ [34,192,288,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38972

def r43236 : Route 9 := (fun mask => (mask,id))

def c43236 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43236 : Upper (D 6) (R 6) [34,192,288,65] 13 := by
  apply FastRouting.sound _ _ [34,192,288,65] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43236 c43236
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43236_3
  · exact m43236_5
  · exact m43236_6
  · exact m43236_9
  · exact m43236_10
  · exact m43236_12

def b43237 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 194 292 74 29 61 93 157 285), lower := (rows 35 194 292 74 16 32 64 128 256), losses := [] }

theorem u43237 : Upper (D 6) (R 6) [34,192,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43238_3 : Upper (D 6) (R 6) [34,192,288,68,3] 13 :=
  permutation_upper _ _ _ [34,192,288,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38944

theorem m43238_5 : Upper (D 6) (R 6) [34,192,288,68,5] 13 :=
  permutation_upper _ _ _ [34,192,288,5,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38953

theorem m43238_6 : Upper (D 6) (R 6) [34,192,288,68,6] 13 :=
  permutation_upper _ _ _ [34,192,288,6,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38958

theorem m43238_9 : Upper (D 6) (R 6) [34,192,288,68,9] 13 :=
  permutation_upper _ _ _ [34,192,288,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38965

theorem m43238_10 : Upper (D 6) (R 6) [34,192,288,68,10] 13 :=
  permutation_upper _ _ _ [34,192,288,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38969

theorem m43238_12 : Upper (D 6) (R 6) [34,192,288,68,12] 13 :=
  permutation_upper _ _ _ [34,192,288,20,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38974

def r43238 : Route 9 := (fun mask => (mask,id))

def c43238 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43238 : Upper (D 6) (R 6) [34,192,288,68] 13 := by
  apply FastRouting.sound _ _ [34,192,288,68] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43238 c43238
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43238_3
  · exact m43238_5
  · exact m43238_6
  · exact m43238_9
  · exact m43238_10
  · exact m43238_12

theorem m43239_3 : Upper (D 6) (R 6) [34,192,288,80,3] 13 :=
  permutation_upper _ _ _ [34,192,288,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38945

theorem m43239_5 : Upper (D 6) (R 6) [34,192,288,80,5] 13 :=
  permutation_upper _ _ _ [34,192,288,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38954

theorem m43239_6 : Upper (D 6) (R 6) [34,192,288,80,6] 13 :=
  permutation_upper _ _ _ [34,192,288,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38959

theorem m43239_9 : Upper (D 6) (R 6) [34,192,288,80,9] 13 :=
  permutation_upper _ _ _ [34,192,288,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38966

theorem m43239_10 : Upper (D 6) (R 6) [34,192,288,80,10] 13 :=
  permutation_upper _ _ _ [34,192,288,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38970

theorem m43239_12 : Upper (D 6) (R 6) [34,192,288,80,12] 13 :=
  permutation_upper _ _ _ [34,192,288,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38975

def r43239 : Route 9 := (fun mask => (mask,id))

def c43239 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43239 : Upper (D 6) (R 6) [34,192,288,80] 13 := by
  apply FastRouting.sound _ _ [34,192,288,80] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43239 c43239
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43239_3
  · exact m43239_5
  · exact m43239_6
  · exact m43239_9
  · exact m43239_10
  · exact m43239_12

def b43240 : PairBound 9 := { available := 61, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 324 11 61 61 125 189 317), lower := (rows 35 194 324 11 16 32 64 128 256), losses := [] }

theorem u43240 : Upper (D 6) (R 6) [34,192,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43241_3 : Upper (D 6) (R 6) [34,192,320,5,3] 13 :=
  permutation_upper _ _ _ [34,192,320,3,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38976

def r43241 : Route 9 := (fun mask => (mask,id))

def c43241 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43241 : Upper (D 6) (R 6) [34,192,320,5] 13 := by
  apply FastRouting.sound _ _ [34,192,320,5] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r43241 c43241
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43241_3
  · exact u38981
  · exact u38982
  · exact u38983
  · exact u38984
  · exact u38985
  · exact u38986
  · exact u38987
  · exact u38988
  · exact u38989

theorem m43242_5 : Upper (D 6) (R 6) [34,192,320,6,5] 13 :=
  permutation_upper _ _ _ [34,192,320,5,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38982

def r43242 : Route 9 := (fun mask => (mask,id))

def c43242 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43242 : Upper (D 6) (R 6) [34,192,320,6] 13 := by
  apply FastRouting.sound _ _ [34,192,320,6] 13 (by decide) (choices 2) [5,9,12,33,36,40] r43242 c43242
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43242_5
  · exact u38990
  · exact u38991
  · exact u38992
  · exact u38993
  · exact u38994

theorem m43243_3 : Upper (D 6) (R 6) [34,192,320,17,3] 13 :=
  permutation_upper _ _ _ [34,192,320,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38977

theorem m43243_5 : Upper (D 6) (R 6) [34,192,320,17,5] 13 :=
  permutation_upper _ _ _ [34,192,320,5,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38983

theorem m43243_6 : Upper (D 6) (R 6) [34,192,320,17,6] 13 :=
  permutation_upper _ _ _ [34,192,320,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38990

def r43243 : Route 9 := (fun mask => (mask,id))

def c43243 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43243 : Upper (D 6) (R 6) [34,192,320,17] 13 := by
  apply FastRouting.sound _ _ [34,192,320,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r43243 c43243
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43243_3
  · exact m43243_5
  · exact m43243_6
  · exact u38995
  · exact u38996
  · exact u38997
  · exact u38998
  · exact u38999
  · exact u39000
  · exact u39001

theorem m43244_5 : Upper (D 6) (R 6) [34,192,320,18,5] 13 :=
  permutation_upper _ _ _ [34,192,320,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38984

theorem m43244_9 : Upper (D 6) (R 6) [34,192,320,18,9] 13 :=
  permutation_upper _ _ _ [34,192,320,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38996

def r43244 : Route 9 := (fun mask => (mask,id))

def c43244 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43244 : Upper (D 6) (R 6) [34,192,320,18] 13 := by
  apply FastRouting.sound _ _ [34,192,320,18] 13 (by decide) (choices 2) [5,9,12,33,36,40] r43244 c43244
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43244_5
  · exact m43244_9
  · exact u39002
  · exact u39003
  · exact u39004
  · exact u39005

theorem m43245_3 : Upper (D 6) (R 6) [34,192,320,20,3] 13 :=
  permutation_upper _ _ _ [34,192,320,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38978

theorem m43245_5 : Upper (D 6) (R 6) [34,192,320,20,5] 13 :=
  permutation_upper _ _ _ [34,192,320,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38985

theorem m43245_6 : Upper (D 6) (R 6) [34,192,320,20,6] 13 :=
  permutation_upper _ _ _ [34,192,320,6,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38991

theorem m43245_9 : Upper (D 6) (R 6) [34,192,320,20,9] 13 :=
  permutation_upper _ _ _ [34,192,320,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38997

theorem m43245_10 : Upper (D 6) (R 6) [34,192,320,20,10] 13 :=
  permutation_upper _ _ _ [34,192,320,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39002

def r43245 : Route 9 := (fun mask => (mask,id))

def c43245 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43245 : Upper (D 6) (R 6) [34,192,320,20] 13 := by
  apply FastRouting.sound _ _ [34,192,320,20] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r43245 c43245
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43245_3
  · exact m43245_5
  · exact m43245_6
  · exact m43245_9
  · exact m43245_10
  · exact u39006
  · exact u39007
  · exact u39008
  · exact u39009
  · exact u39010

def b43246 : PairBound 9 := { available := 31, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 324 41 31 63 95 159 287), lower := (rows 35 194 324 41 16 32 64 128 256), losses := [] }

theorem u43246 : Upper (D 6) (R 6) [34,192,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43247 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 194 324 42 29 61 93 157 285), lower := (rows 35 194 324 42 16 32 64 128 256), losses := [] }

theorem u43247 : Upper (D 6) (R 6) [34,192,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43248_3 : Upper (D 6) (R 6) [34,192,320,36,3] 13 :=
  permutation_upper _ _ _ [34,192,320,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38979

theorem m43248_5 : Upper (D 6) (R 6) [34,192,320,36,5] 13 :=
  permutation_upper _ _ _ [34,192,320,5,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38988

theorem m43248_6 : Upper (D 6) (R 6) [34,192,320,36,6] 13 :=
  permutation_upper _ _ _ [34,192,320,6,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38993

theorem m43248_9 : Upper (D 6) (R 6) [34,192,320,36,9] 13 :=
  permutation_upper _ _ _ [34,192,320,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39000

theorem m43248_10 : Upper (D 6) (R 6) [34,192,320,36,10] 13 :=
  permutation_upper _ _ _ [34,192,320,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39004

theorem m43248_12 : Upper (D 6) (R 6) [34,192,320,36,12] 13 :=
  permutation_upper _ _ _ [34,192,320,20,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39009

def r43248 : Route 9 := (fun mask => (mask,id))

def c43248 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43248 : Upper (D 6) (R 6) [34,192,320,36] 13 := by
  apply FastRouting.sound _ _ [34,192,320,36] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43248 c43248
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43248_3
  · exact m43248_5
  · exact m43248_6
  · exact m43248_9
  · exact m43248_10
  · exact m43248_12

theorem m43249_3 : Upper (D 6) (R 6) [34,192,320,48,3] 13 :=
  permutation_upper _ _ _ [34,192,320,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38980

theorem m43249_5 : Upper (D 6) (R 6) [34,192,320,48,5] 13 :=
  permutation_upper _ _ _ [34,192,320,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38989

theorem m43249_6 : Upper (D 6) (R 6) [34,192,320,48,6] 13 :=
  permutation_upper _ _ _ [34,192,320,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38994

theorem m43249_9 : Upper (D 6) (R 6) [34,192,320,48,9] 13 :=
  permutation_upper _ _ _ [34,192,320,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39001

theorem m43249_10 : Upper (D 6) (R 6) [34,192,320,48,10] 13 :=
  permutation_upper _ _ _ [34,192,320,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39005

theorem m43249_12 : Upper (D 6) (R 6) [34,192,320,48,12] 13 :=
  permutation_upper _ _ _ [34,192,320,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39010

def r43249 : Route 9 := (fun mask => (mask,id))

def c43249 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43249 : Upper (D 6) (R 6) [34,192,320,48] 13 := by
  apply FastRouting.sound _ _ [34,192,320,48] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43249 c43249
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43249_3
  · exact m43249_5
  · exact m43249_6
  · exact m43249_9
  · exact m43249_10
  · exact m43249_12

def b43250 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 36 },{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6),(3,2),(3,5)], upper := (rows 35 386 44 11 85 117 85 213 341), lower := (rows 35 386 44 11 16 32 64 128 256), losses := [] }

theorem u43250 : Upper (D 6) (R 6) [34,384,40,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43251 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 12, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 386 44 13 87 119 87 215 343), lower := (rows 35 386 44 13 16 32 64 128 256), losses := [] }

theorem u43251 : Upper (D 6) (R 6) [34,384,40,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43252 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 12, targets := 1 },{ cop := 0, region := 12, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 35 386 44 14 85 117 85 213 341), lower := (rows 35 386 44 14 16 32 64 128 256), losses := [] }

theorem u43252 : Upper (D 6) (R 6) [34,384,40,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43253 : Route 9 := (fun mask => (mask,id))

def c43253 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43253 : Upper (D 6) (R 6) [34,384,40,17] 13 := by
  apply FastRouting.sound _ _ [34,384,40,17] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43253 c43253
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39011
  · exact u39012
  · exact u39013
  · exact u39014
  · exact u39015
  · exact u39016

def r43254 : Route 9 := (fun mask => (mask,id))

def c43254 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43254 : Upper (D 6) (R 6) [34,384,40,18] 13 := by
  apply FastRouting.sound _ _ [34,384,40,18] 13 (by decide) (choices 2) [5,65,68] r43254 c43254
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39017
  · exact u39018
  · exact u39019

def r43255 : Route 9 := (fun mask => (mask,id))

def c43255 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43255 : Upper (D 6) (R 6) [34,384,40,20] 13 := by
  apply FastRouting.sound _ _ [34,384,40,20] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43255 c43255
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39020
  · exact u39021
  · exact u39022
  · exact u39023
  · exact u39024
  · exact u39025

def r43256 : Route 9 := (fun mask => (mask,id))

def c43256 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43256 : Upper (D 6) (R 6) [34,384,40,65] 13 := by
  apply FastRouting.sound _ _ [34,384,40,65] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43256 c43256
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39026
  · exact u39027
  · exact u39028
  · exact u39029
  · exact u39030
  · exact u39031

def r43257 : Route 9 := (fun mask => (mask,id))

def c43257 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43257 : Upper (D 6) (R 6) [34,384,40,66] 13 := by
  apply FastRouting.sound _ _ [34,384,40,66] 13 (by decide) (choices 2) [5,65,68] r43257 c43257
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39032
  · exact u39033
  · exact u39034

def r43258 : Route 9 := (fun mask => (mask,id))

def c43258 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43258 : Upper (D 6) (R 6) [34,384,40,68] 13 := by
  apply FastRouting.sound _ _ [34,384,40,68] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43258 c43258
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39035
  · exact u39036
  · exact u39037
  · exact u39038
  · exact u39039
  · exact u39040

def r43259 : Route 9 := (fun mask => (mask,id))

def c43259 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43259 : Upper (D 6) (R 6) [34,384,40,80] 13 := by
  apply FastRouting.sound _ _ [34,384,40,80] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43259 c43259
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39041
  · exact u39042
  · exact u39043
  · exact u39044
  · exact u39045
  · exact u39046

#print axioms u43259
end Delivery.IrregularNine14.P06
