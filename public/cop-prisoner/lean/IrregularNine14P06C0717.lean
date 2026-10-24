import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0632
import IrregularNine14P06C0633
import IrregularNine14P06C0634
import IrregularNine14P06C0635
import IrregularNine14P06C0636
import IrregularNine14P06C0637

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m43020_5 : Upper (D 6) (R 6) [34,132,288,18,5] 13 :=
  permutation_upper _ _ _ [34,132,288,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37926

theorem m43020_9 : Upper (D 6) (R 6) [34,132,288,18,9] 13 :=
  permutation_upper _ _ _ [34,132,288,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37934

def r43020 : Route 9 := (fun mask => (mask,id))

def c43020 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43020 : Upper (D 6) (R 6) [34,132,288,18] 13 := by
  apply FastRouting.sound _ _ [34,132,288,18] 13 (by decide) (choices 2) [5,9,12,65,68,72] r43020 c43020
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43020_5
  · exact m43020_9
  · exact u37940
  · exact u37941
  · exact u37942
  · exact u37943

theorem m43021_3 : Upper (D 6) (R 6) [34,132,288,20,3] 13 :=
  permutation_upper _ _ _ [34,132,288,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37921

theorem m43021_9 : Upper (D 6) (R 6) [34,132,288,20,9] 13 :=
  permutation_upper _ _ _ [34,132,288,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37935

theorem m43021_10 : Upper (D 6) (R 6) [34,132,288,20,10] 13 :=
  permutation_upper _ _ _ [34,132,288,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37940

def r43021 : Route 9 := (fun mask => (mask,id))

def c43021 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43021 : Upper (D 6) (R 6) [34,132,288,20] 13 := by
  apply FastRouting.sound _ _ [34,132,288,20] 13 (by decide) (choices 2) [3,9,10,65,66,72] r43021 c43021
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43021_3
  · exact m43021_9
  · exact m43021_10
  · exact u37944
  · exact u37945
  · exact u37946

theorem m43022_3 : Upper (D 6) (R 6) [34,132,288,65,3] 13 :=
  permutation_upper _ _ _ [34,132,288,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37922

theorem m43022_5 : Upper (D 6) (R 6) [34,132,288,65,5] 13 :=
  permutation_upper _ _ _ [34,132,288,5,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37927

theorem m43022_6 : Upper (D 6) (R 6) [34,132,288,65,6] 13 :=
  permutation_upper _ _ _ [34,132,288,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37931

theorem m43022_9 : Upper (D 6) (R 6) [34,132,288,65,9] 13 :=
  permutation_upper _ _ _ [34,132,288,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37936

theorem m43022_10 : Upper (D 6) (R 6) [34,132,288,65,10] 13 :=
  permutation_upper _ _ _ [34,132,288,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37941

theorem m43022_12 : Upper (D 6) (R 6) [34,132,288,65,12] 13 :=
  permutation_upper _ _ _ [34,132,288,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37944

def r43022 : Route 9 := (fun mask => (mask,id))

def c43022 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43022 : Upper (D 6) (R 6) [34,132,288,65] 13 := by
  apply FastRouting.sound _ _ [34,132,288,65] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43022 c43022
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43022_3
  · exact m43022_5
  · exact m43022_6
  · exact m43022_9
  · exact m43022_10
  · exact m43022_12
  · exact u37947
  · exact u37948
  · exact u37949
  · exact u37950

theorem m43023_5 : Upper (D 6) (R 6) [34,132,288,66,5] 13 :=
  permutation_upper _ _ _ [34,132,288,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37928

theorem m43023_9 : Upper (D 6) (R 6) [34,132,288,66,9] 13 :=
  permutation_upper _ _ _ [34,132,288,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37937

theorem m43023_12 : Upper (D 6) (R 6) [34,132,288,66,12] 13 :=
  permutation_upper _ _ _ [34,132,288,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37945

theorem m43023_65 : Upper (D 6) (R 6) [34,132,288,66,65] 13 :=
  permutation_upper _ _ _ [34,132,288,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37948

def r43023 : Route 9 := (fun mask => (mask,id))

def c43023 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43023 : Upper (D 6) (R 6) [34,132,288,66] 13 := by
  apply FastRouting.sound _ _ [34,132,288,66] 13 (by decide) (choices 2) [5,9,12,65,68,72] r43023 c43023
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43023_5
  · exact m43023_9
  · exact m43023_12
  · exact m43023_65
  · exact u37951
  · exact u37952

theorem m43024_3 : Upper (D 6) (R 6) [34,132,288,68,3] 13 :=
  permutation_upper _ _ _ [34,132,288,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37923

theorem m43024_9 : Upper (D 6) (R 6) [34,132,288,68,9] 13 :=
  permutation_upper _ _ _ [34,132,288,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37938

theorem m43024_10 : Upper (D 6) (R 6) [34,132,288,68,10] 13 :=
  permutation_upper _ _ _ [34,132,288,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37942

theorem m43024_65 : Upper (D 6) (R 6) [34,132,288,68,65] 13 :=
  permutation_upper _ _ _ [34,132,288,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37949

theorem m43024_66 : Upper (D 6) (R 6) [34,132,288,68,66] 13 :=
  permutation_upper _ _ _ [34,132,288,66,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37951

def r43024 : Route 9 := (fun mask => (mask,id))

def c43024 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43024 : Upper (D 6) (R 6) [34,132,288,68] 13 := by
  apply FastRouting.sound _ _ [34,132,288,68] 13 (by decide) (choices 2) [3,9,10,65,66,72] r43024 c43024
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43024_3
  · exact m43024_9
  · exact m43024_10
  · exact m43024_65
  · exact m43024_66
  · exact u37953

theorem m43025_3 : Upper (D 6) (R 6) [34,132,288,80,3] 13 :=
  permutation_upper _ _ _ [34,132,288,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37924

theorem m43025_5 : Upper (D 6) (R 6) [34,132,288,80,5] 13 :=
  permutation_upper _ _ _ [34,132,288,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37929

theorem m43025_6 : Upper (D 6) (R 6) [34,132,288,80,6] 13 :=
  permutation_upper _ _ _ [34,132,288,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37932

theorem m43025_9 : Upper (D 6) (R 6) [34,132,288,80,9] 13 :=
  permutation_upper _ _ _ [34,132,288,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37939

theorem m43025_10 : Upper (D 6) (R 6) [34,132,288,80,10] 13 :=
  permutation_upper _ _ _ [34,132,288,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37943

theorem m43025_12 : Upper (D 6) (R 6) [34,132,288,80,12] 13 :=
  permutation_upper _ _ _ [34,132,288,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37946

theorem m43025_65 : Upper (D 6) (R 6) [34,132,288,80,65] 13 :=
  permutation_upper _ _ _ [34,132,288,65,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37950

theorem m43025_66 : Upper (D 6) (R 6) [34,132,288,80,66] 13 :=
  permutation_upper _ _ _ [34,132,288,66,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37952

theorem m43025_68 : Upper (D 6) (R 6) [34,132,288,80,68] 13 :=
  permutation_upper _ _ _ [34,132,288,68,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37953

def r43025 : Route 9 := (fun mask => (mask,id))

def c43025 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43025 : Upper (D 6) (R 6) [34,132,288,80] 13 := by
  apply FastRouting.sound _ _ [34,132,288,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43025 c43025
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43025_3
  · exact m43025_5
  · exact m43025_6
  · exact m43025_9
  · exact m43025_10
  · exact m43025_12
  · exact m43025_65
  · exact m43025_66
  · exact m43025_68
  · exact u37954

def b43026 : PairBound 9 := { available := 125, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 324 11 125 125 125 253 381), lower := (rows 35 134 324 11 16 32 64 128 256), losses := [] }

theorem u43026 : Upper (D 6) (R 6) [34,132,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43027_3 : Upper (D 6) (R 6) [34,132,320,5,3] 13 :=
  permutation_upper _ _ _ [34,132,320,3,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37955

def r43027 : Route 9 := (fun mask => (mask,id))

def c43027 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43027 : Upper (D 6) (R 6) [34,132,320,5] 13 := by
  apply FastRouting.sound _ _ [34,132,320,5] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r43027 c43027
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43027_3
  · exact u37963
  · exact u37964
  · exact u37965
  · exact u37966
  · exact u37967
  · exact u37968
  · exact u37969
  · exact u37970
  · exact u37971

def b43028 : PairBound 9 := { available := 121, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 324 14 121 121 121 249 377), lower := (rows 35 134 324 14 16 32 64 128 256), losses := [] }

theorem u43028 : Upper (D 6) (R 6) [34,132,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43029_3 : Upper (D 6) (R 6) [34,132,320,17,3] 13 :=
  permutation_upper _ _ _ [34,132,320,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37956

theorem m43029_5 : Upper (D 6) (R 6) [34,132,320,17,5] 13 :=
  permutation_upper _ _ _ [34,132,320,5,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37963

theorem m43029_6 : Upper (D 6) (R 6) [34,132,320,17,6] 13 :=
  permutation_upper _ _ _ [34,132,320,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37972

def r43029 : Route 9 := (fun mask => (mask,id))

def c43029 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43029 : Upper (D 6) (R 6) [34,132,320,17] 13 := by
  apply FastRouting.sound _ _ [34,132,320,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r43029 c43029
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43029_3
  · exact m43029_5
  · exact m43029_6
  · exact u37977
  · exact u37978
  · exact u37979
  · exact u37980
  · exact u37981
  · exact u37982
  · exact u37983
  · exact u37984
  · exact u37985
  · exact u37986
  · exact u37987
  · exact u37988

theorem m43030_5 : Upper (D 6) (R 6) [34,132,320,18,5] 13 :=
  permutation_upper _ _ _ [34,132,320,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37964

theorem m43030_9 : Upper (D 6) (R 6) [34,132,320,18,9] 13 :=
  permutation_upper _ _ _ [34,132,320,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37978

def r43030 : Route 9 := (fun mask => (mask,id))

def c43030 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43030 : Upper (D 6) (R 6) [34,132,320,18] 13 := by
  apply FastRouting.sound _ _ [34,132,320,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r43030 c43030
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43030_5
  · exact m43030_9
  · exact u37989
  · exact u37990
  · exact u37991
  · exact u37992
  · exact u37993
  · exact u37994
  · exact u37995
  · exact u37996

theorem m43031_3 : Upper (D 6) (R 6) [34,132,320,20,3] 13 :=
  permutation_upper _ _ _ [34,132,320,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37957

theorem m43031_9 : Upper (D 6) (R 6) [34,132,320,20,9] 13 :=
  permutation_upper _ _ _ [34,132,320,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37979

theorem m43031_10 : Upper (D 6) (R 6) [34,132,320,20,10] 13 :=
  permutation_upper _ _ _ [34,132,320,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37989

def r43031 : Route 9 := (fun mask => (mask,id))

def c43031 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43031 : Upper (D 6) (R 6) [34,132,320,20] 13 := by
  apply FastRouting.sound _ _ [34,132,320,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r43031 c43031
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43031_3
  · exact m43031_9
  · exact m43031_10
  · exact u37997
  · exact u37998
  · exact u37999
  · exact u38000
  · exact u38001
  · exact u38002
  · exact u38003

def b43032 : PairBound 9 := { available := 95, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 324 41 95 127 95 223 351), lower := (rows 35 134 324 41 16 32 64 128 256), losses := [] }

theorem u43032 : Upper (D 6) (R 6) [34,132,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43033 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 134 324 42 93 125 93 221 349), lower := (rows 35 134 324 42 16 32 64 128 256), losses := [] }

theorem u43033 : Upper (D 6) (R 6) [34,132,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43034_3 : Upper (D 6) (R 6) [34,132,320,36,3] 13 :=
  permutation_upper _ _ _ [34,132,320,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37958

theorem m43034_9 : Upper (D 6) (R 6) [34,132,320,36,9] 13 :=
  permutation_upper _ _ _ [34,132,320,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37982

theorem m43034_10 : Upper (D 6) (R 6) [34,132,320,36,10] 13 :=
  permutation_upper _ _ _ [34,132,320,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37991

def r43034 : Route 9 := (fun mask => (mask,id))

def c43034 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43034 : Upper (D 6) (R 6) [34,132,320,36] 13 := by
  apply FastRouting.sound _ _ [34,132,320,36] 13 (by decide) (choices 2) [3,9,10,65,66,72] r43034 c43034
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43034_3
  · exact m43034_9
  · exact m43034_10
  · exact u38009
  · exact u38010
  · exact u38011

theorem m43035_3 : Upper (D 6) (R 6) [34,132,320,48,3] 13 :=
  permutation_upper _ _ _ [34,132,320,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37959

theorem m43035_5 : Upper (D 6) (R 6) [34,132,320,48,5] 13 :=
  permutation_upper _ _ _ [34,132,320,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37967

theorem m43035_6 : Upper (D 6) (R 6) [34,132,320,48,6] 13 :=
  permutation_upper _ _ _ [34,132,320,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37973

theorem m43035_9 : Upper (D 6) (R 6) [34,132,320,48,9] 13 :=
  permutation_upper _ _ _ [34,132,320,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37983

theorem m43035_10 : Upper (D 6) (R 6) [34,132,320,48,10] 13 :=
  permutation_upper _ _ _ [34,132,320,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37992

theorem m43035_12 : Upper (D 6) (R 6) [34,132,320,48,12] 13 :=
  permutation_upper _ _ _ [34,132,320,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37999

def r43035 : Route 9 := (fun mask => (mask,id))

def c43035 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43035 : Upper (D 6) (R 6) [34,132,320,48] 13 := by
  apply FastRouting.sound _ _ [34,132,320,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43035 c43035
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43035_3
  · exact m43035_5
  · exact m43035_6
  · exact m43035_9
  · exact m43035_10
  · exact m43035_12
  · exact u38012
  · exact u38013
  · exact u38014
  · exact u38015

theorem m43036_3 : Upper (D 6) (R 6) [34,132,320,65,3] 13 :=
  permutation_upper _ _ _ [34,132,320,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37960

theorem m43036_5 : Upper (D 6) (R 6) [34,132,320,65,5] 13 :=
  permutation_upper _ _ _ [34,132,320,5,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37968

theorem m43036_6 : Upper (D 6) (R 6) [34,132,320,65,6] 13 :=
  permutation_upper _ _ _ [34,132,320,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37974

theorem m43036_9 : Upper (D 6) (R 6) [34,132,320,65,9] 13 :=
  permutation_upper _ _ _ [34,132,320,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37984

theorem m43036_10 : Upper (D 6) (R 6) [34,132,320,65,10] 13 :=
  permutation_upper _ _ _ [34,132,320,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37993

theorem m43036_12 : Upper (D 6) (R 6) [34,132,320,65,12] 13 :=
  permutation_upper _ _ _ [34,132,320,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38000

theorem m43036_33 : Upper (D 6) (R 6) [34,132,320,65,33] 13 :=
  permutation_upper _ _ _ [34,132,320,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38004

theorem m43036_34 : Upper (D 6) (R 6) [34,132,320,65,34] 13 :=
  permutation_upper _ _ _ [34,132,320,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38007

theorem m43036_36 : Upper (D 6) (R 6) [34,132,320,65,36] 13 :=
  permutation_upper _ _ _ [34,132,320,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38009

theorem m43036_40 : Upper (D 6) (R 6) [34,132,320,65,40] 13 :=
  permutation_upper _ _ _ [34,132,320,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38012

def r43036 : Route 9 := (fun mask => (mask,id))

def c43036 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43036 : Upper (D 6) (R 6) [34,132,320,65] 13 := by
  apply FastRouting.sound _ _ [34,132,320,65] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r43036 c43036
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43036_3
  · exact m43036_5
  · exact m43036_6
  · exact m43036_9
  · exact m43036_10
  · exact m43036_12
  · exact m43036_33
  · exact m43036_34
  · exact m43036_36
  · exact m43036_40

theorem m43037_5 : Upper (D 6) (R 6) [34,132,320,66,5] 13 :=
  permutation_upper _ _ _ [34,132,320,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37969

theorem m43037_9 : Upper (D 6) (R 6) [34,132,320,66,9] 13 :=
  permutation_upper _ _ _ [34,132,320,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37985

theorem m43037_12 : Upper (D 6) (R 6) [34,132,320,66,12] 13 :=
  permutation_upper _ _ _ [34,132,320,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38001

theorem m43037_33 : Upper (D 6) (R 6) [34,132,320,66,33] 13 :=
  permutation_upper _ _ _ [34,132,320,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38005

theorem m43037_36 : Upper (D 6) (R 6) [34,132,320,66,36] 13 :=
  permutation_upper _ _ _ [34,132,320,36,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38010

theorem m43037_40 : Upper (D 6) (R 6) [34,132,320,66,40] 13 :=
  permutation_upper _ _ _ [34,132,320,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38013

def r43037 : Route 9 := (fun mask => (mask,id))

def c43037 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43037 : Upper (D 6) (R 6) [34,132,320,66] 13 := by
  apply FastRouting.sound _ _ [34,132,320,66] 13 (by decide) (choices 2) [5,9,12,33,36,40] r43037 c43037
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43037_5
  · exact m43037_9
  · exact m43037_12
  · exact m43037_33
  · exact m43037_36
  · exact m43037_40

def b43038 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 134 324 76 59 59 123 187 315), lower := (rows 35 134 324 76 16 32 64 128 256), losses := [] }

theorem u43038 : Upper (D 6) (R 6) [34,132,320,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43039_3 : Upper (D 6) (R 6) [34,132,320,80,3] 13 :=
  permutation_upper _ _ _ [34,132,320,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37961

theorem m43039_5 : Upper (D 6) (R 6) [34,132,320,80,5] 13 :=
  permutation_upper _ _ _ [34,132,320,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37970

theorem m43039_6 : Upper (D 6) (R 6) [34,132,320,80,6] 13 :=
  permutation_upper _ _ _ [34,132,320,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37975

theorem m43039_9 : Upper (D 6) (R 6) [34,132,320,80,9] 13 :=
  permutation_upper _ _ _ [34,132,320,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37987

theorem m43039_10 : Upper (D 6) (R 6) [34,132,320,80,10] 13 :=
  permutation_upper _ _ _ [34,132,320,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37995

theorem m43039_12 : Upper (D 6) (R 6) [34,132,320,80,12] 13 :=
  permutation_upper _ _ _ [34,132,320,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38002

theorem m43039_33 : Upper (D 6) (R 6) [34,132,320,80,33] 13 :=
  permutation_upper _ _ _ [34,132,320,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38006

theorem m43039_34 : Upper (D 6) (R 6) [34,132,320,80,34] 13 :=
  permutation_upper _ _ _ [34,132,320,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38008

theorem m43039_36 : Upper (D 6) (R 6) [34,132,320,80,36] 13 :=
  permutation_upper _ _ _ [34,132,320,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38011

theorem m43039_40 : Upper (D 6) (R 6) [34,132,320,80,40] 13 :=
  permutation_upper _ _ _ [34,132,320,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38015

def r43039 : Route 9 := (fun mask => (mask,id))

def c43039 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43039 : Upper (D 6) (R 6) [34,132,320,80] 13 := by
  apply FastRouting.sound _ _ [34,132,320,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r43039 c43039
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43039_3
  · exact m43039_5
  · exact m43039_6
  · exact m43039_9
  · exact m43039_10
  · exact m43039_12
  · exact m43039_33
  · exact m43039_34
  · exact m43039_36
  · exact m43039_40

theorem m43040_3 : Upper (D 6) (R 6) [34,132,320,96,3] 13 :=
  permutation_upper _ _ _ [34,132,320,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37962

theorem m43040_5 : Upper (D 6) (R 6) [34,132,320,96,5] 13 :=
  permutation_upper _ _ _ [34,132,320,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37971

theorem m43040_6 : Upper (D 6) (R 6) [34,132,320,96,6] 13 :=
  permutation_upper _ _ _ [34,132,320,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37976

theorem m43040_9 : Upper (D 6) (R 6) [34,132,320,96,9] 13 :=
  permutation_upper _ _ _ [34,132,320,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37988

theorem m43040_10 : Upper (D 6) (R 6) [34,132,320,96,10] 13 :=
  permutation_upper _ _ _ [34,132,320,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37996

theorem m43040_12 : Upper (D 6) (R 6) [34,132,320,96,12] 13 :=
  permutation_upper _ _ _ [34,132,320,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38003

def r43040 : Route 9 := (fun mask => (mask,id))

def c43040 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43040 : Upper (D 6) (R 6) [34,132,320,96] 13 := by
  apply FastRouting.sound _ _ [34,132,320,96] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43040 c43040
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43040_3
  · exact m43040_5
  · exact m43040_6
  · exact m43040_9
  · exact m43040_10
  · exact m43040_12

def b43041 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 138 52 11 341 357 325 453 325), lower := (rows 35 138 52 11 16 32 64 128 256), losses := [] }

theorem u43041 : Upper (D 6) (R 6) [34,136,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43042 : Route 9 := (fun mask => (mask,id))

def c43042 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43042 : Upper (D 6) (R 6) [34,136,48,5] 13 := by
  apply FastRouting.sound _ _ [34,136,48,5] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43042 c43042
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38016
  · exact u38017
  · exact u38018
  · exact u38019
  · exact u38020
  · exact u38021
  · exact u38022
  · exact u38023
  · exact u38024
  · exact u38025

def r43043 : Route 9 := (fun mask => (mask,id))

def c43043 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43043 : Upper (D 6) (R 6) [34,136,48,6] 13 := by
  apply FastRouting.sound _ _ [34,136,48,6] 13 (by decide) (choices 2) [5,65,68,257,260,320] r43043 c43043
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38026
  · exact u38027
  · exact u38028
  · exact u38029
  · exact u38030
  · exact u38031

def r43044 : Route 9 := (fun mask => (mask,id))

def c43044 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43044 : Upper (D 6) (R 6) [34,136,48,65] 13 := by
  apply FastRouting.sound _ _ [34,136,48,65] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43044 c43044
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38032
  · exact u38033
  · exact u38034
  · exact u38035
  · exact u38036
  · exact u38037
  · exact u38038
  · exact u38039
  · exact u38040
  · exact u38041

def r43045 : Route 9 := (fun mask => (mask,id))

def c43045 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43045 : Upper (D 6) (R 6) [34,136,48,66] 13 := by
  apply FastRouting.sound _ _ [34,136,48,66] 13 (by decide) (choices 2) [5,65,68,257,260,320] r43045 c43045
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38042
  · exact u38043
  · exact u38044
  · exact u38045
  · exact u38046
  · exact u38047

def r43046 : Route 9 := (fun mask => (mask,id))

def c43046 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43046 : Upper (D 6) (R 6) [34,136,48,68] 13 := by
  apply FastRouting.sound _ _ [34,136,48,68] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43046 c43046
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38048
  · exact u38049
  · exact u38050
  · exact u38051
  · exact u38052
  · exact u38053
  · exact u38054
  · exact u38055
  · exact u38056
  · exact u38057

def r43047 : Route 9 := (fun mask => (mask,id))

def c43047 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43047 : Upper (D 6) (R 6) [34,136,48,257] 13 := by
  apply FastRouting.sound _ _ [34,136,48,257] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43047 c43047
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38058
  · exact u38059
  · exact u38060
  · exact u38061
  · exact u38062
  · exact u38063

def r43048 : Route 9 := (fun mask => (mask,id))

def c43048 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43048 : Upper (D 6) (R 6) [34,136,48,258] 13 := by
  apply FastRouting.sound _ _ [34,136,48,258] 13 (by decide) (choices 2) [5,65,68] r43048 c43048
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38064
  · exact u38065
  · exact u38066

def r43049 : Route 9 := (fun mask => (mask,id))

def c43049 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43049 : Upper (D 6) (R 6) [34,136,48,260] 13 := by
  apply FastRouting.sound _ _ [34,136,48,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43049 c43049
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38067
  · exact u38068
  · exact u38069
  · exact u38070
  · exact u38071
  · exact u38072

def r43050 : Route 9 := (fun mask => (mask,id))

def c43050 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43050 : Upper (D 6) (R 6) [34,136,48,320] 13 := by
  apply FastRouting.sound _ _ [34,136,48,320] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43050 c43050
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38073
  · exact u38074
  · exact u38075
  · exact u38076
  · exact u38077
  · exact u38078

theorem m43051_65 : Upper (D 6) (R 6) [34,136,66,5,65] 13 :=
  permutation_upper _ _ _ [34,136,66,5,36] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38081

theorem m43051_68 : Upper (D 6) (R 6) [34,136,66,5,68] 13 :=
  permutation_upper _ _ _ [34,136,66,5,33] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38080

theorem m43051_260 : Upper (D 6) (R 6) [34,136,66,5,260] 13 :=
  permutation_upper _ _ _ [34,136,66,5,257] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38083

theorem m43051_320 : Upper (D 6) (R 6) [34,136,66,5,320] 13 :=
  permutation_upper _ _ _ [34,136,66,5,288] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38084

def r43051 : Route 9 := (fun mask => (mask,id))

def c43051 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43051 : Upper (D 6) (R 6) [34,136,66,5] 13 := by
  apply FastRouting.sound _ _ [34,136,66,5] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r43051 c43051
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38079
  · exact u38080
  · exact u38081
  · exact m43051_65
  · exact m43051_68
  · exact u38082
  · exact u38083
  · exact m43051_260
  · exact u38084
  · exact m43051_320

def r43052 : Route 9 := (fun mask => (mask,id))

def c43052 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43052 : Upper (D 6) (R 6) [34,136,66,17] 13 := by
  apply FastRouting.sound _ _ [34,136,66,17] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r43052 c43052
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38085
  · exact u38086
  · exact u38087
  · exact u38088
  · exact u38089
  · exact u38090
  · exact u38091
  · exact u38092
  · exact u38093
  · exact u38094

def b43053 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 138 70 41 341 373 341 469 341), lower := (rows 35 138 70 41 16 32 64 128 256), losses := [] }

theorem u43053 : Upper (D 6) (R 6) [34,136,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43054 : Route 9 := (fun mask => (mask,id))

def c43054 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43054 : Upper (D 6) (R 6) [34,136,66,36] 13 := by
  apply FastRouting.sound _ _ [34,136,66,36] 13 (by decide) (choices 2) [5,65,68,257,260,320] r43054 c43054
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38095
  · exact u38096
  · exact u38097
  · exact u38098
  · exact u38099
  · exact u38100

def r43055 : Route 9 := (fun mask => (mask,id))

def c43055 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43055 : Upper (D 6) (R 6) [34,136,66,48] 13 := by
  apply FastRouting.sound _ _ [34,136,66,48] 13 (by decide) (choices 2) [5,65,68,257,260,320] r43055 c43055
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38101
  · exact u38102
  · exact u38103
  · exact u38104
  · exact u38105
  · exact u38106

def b43056 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 305, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 138 70 104 277 309 341 405 277), lower := (rows 35 138 70 104 16 32 64 128 256), losses := [] }

theorem u43056 : Upper (D 6) (R 6) [34,136,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43057 : Route 9 := (fun mask => (mask,id))

def c43057 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43057 : Upper (D 6) (R 6) [34,136,66,257] 13 := by
  apply FastRouting.sound _ _ [34,136,66,257] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43057 c43057
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38107
  · exact u38108
  · exact u38109
  · exact u38110
  · exact u38111
  · exact u38112

theorem m43058_65 : Upper (D 6) (R 6) [34,136,66,272,65] 13 :=
  permutation_upper _ _ _ [34,136,66,272,36] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38115

theorem m43058_68 : Upper (D 6) (R 6) [34,136,66,272,68] 13 :=
  permutation_upper _ _ _ [34,136,66,272,33] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38114

def r43058 : Route 9 := (fun mask => (mask,id))

def c43058 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43058 : Upper (D 6) (R 6) [34,136,66,272] 13 := by
  apply FastRouting.sound _ _ [34,136,66,272] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43058 c43058
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38113
  · exact u38114
  · exact u38115
  · exact m43058_65
  · exact m43058_68
  · exact u38116

def r43059 : Route 9 := (fun mask => (mask,id))

def c43059 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43059 : Upper (D 6) (R 6) [34,136,66,288] 13 := by
  apply FastRouting.sound _ _ [34,136,66,288] 13 (by decide) (choices 2) [5,65,68] r43059 c43059
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38117
  · exact u38118
  · exact u38119

def b43060 : PairBound 9 := { available := 357, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 138 84 11 373 357 357 485 357), lower := (rows 35 138 84 11 16 32 64 128 256), losses := [] }

theorem u43060 : Upper (D 6) (R 6) [34,136,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43061 : Route 9 := (fun mask => (mask,id))

def c43061 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43061 : Upper (D 6) (R 6) [34,136,80,5] 13 := by
  apply FastRouting.sound _ _ [34,136,80,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43061 c43061
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38120
  · exact u38121
  · exact u38122
  · exact u38123
  · exact u38124
  · exact u38125
  · exact u38126
  · exact u38127
  · exact u38128
  · exact u38129
  · exact u38130
  · exact u38131
  · exact u38132
  · exact u38133
  · exact u38134

def r43062 : Route 9 := (fun mask => (mask,id))

def c43062 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43062 : Upper (D 6) (R 6) [34,136,80,6] 13 := by
  apply FastRouting.sound _ _ [34,136,80,6] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r43062 c43062
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38135
  · exact u38136
  · exact u38137
  · exact u38138
  · exact u38139
  · exact u38140
  · exact u38141
  · exact u38142
  · exact u38143
  · exact u38144

def b43063 : PairBound 9 := { available := 327, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 138 84 41 343 359 327 455 327), lower := (rows 35 138 84 41 16 32 64 128 256), losses := [] }

theorem u43063 : Upper (D 6) (R 6) [34,136,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43064 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 8, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 138 84 42 341 357 325 453 325), lower := (rows 35 138 84 42 16 32 64 128 256), losses := [] }

theorem u43064 : Upper (D 6) (R 6) [34,136,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43065 : Route 9 := (fun mask => (mask,id))

def c43065 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43065 : Upper (D 6) (R 6) [34,136,80,36] 13 := by
  apply FastRouting.sound _ _ [34,136,80,36] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43065 c43065
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38145
  · exact u38146
  · exact u38147
  · exact u38148
  · exact u38149
  · exact u38150
  · exact u38151
  · exact u38152
  · exact u38153
  · exact u38154

def r43066 : Route 9 := (fun mask => (mask,id))

def c43066 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43066 : Upper (D 6) (R 6) [34,136,80,65] 13 := by
  apply FastRouting.sound _ _ [34,136,80,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r43066 c43066
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38155
  · exact u38156
  · exact u38157
  · exact u38158
  · exact u38159
  · exact u38160
  · exact u38161
  · exact u38162
  · exact u38163
  · exact u38164

def r43067 : Route 9 := (fun mask => (mask,id))

def c43067 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43067 : Upper (D 6) (R 6) [34,136,80,66] 13 := by
  apply FastRouting.sound _ _ [34,136,80,66] 13 (by decide) (choices 2) [5,33,36,257,260,288] r43067 c43067
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38165
  · exact u38166
  · exact u38167
  · exact u38168
  · exact u38169
  · exact u38170

def b43068 : PairBound 9 := { available := 295, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 84 76 311 295 359 423 295), lower := (rows 35 138 84 76 16 32 64 128 256), losses := [] }

theorem u43068 : Upper (D 6) (R 6) [34,136,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43069 : Route 9 := (fun mask => (mask,id))

def c43069 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43069 : Upper (D 6) (R 6) [34,136,80,96] 13 := by
  apply FastRouting.sound _ _ [34,136,80,96] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43069 c43069
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38171
  · exact u38172
  · exact u38173
  · exact u38174
  · exact u38175
  · exact u38176

def r43070 : Route 9 := (fun mask => (mask,id))

def c43070 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43070 : Upper (D 6) (R 6) [34,136,80,257] 13 := by
  apply FastRouting.sound _ _ [34,136,80,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43070 c43070
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38177
  · exact u38178
  · exact u38179
  · exact u38180
  · exact u38181
  · exact u38182
  · exact u38183
  · exact u38184
  · exact u38185
  · exact u38186

def r43071 : Route 9 := (fun mask => (mask,id))

def c43071 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43071 : Upper (D 6) (R 6) [34,136,80,258] 13 := by
  apply FastRouting.sound _ _ [34,136,80,258] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43071 c43071
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38187
  · exact u38188
  · exact u38189
  · exact u38190
  · exact u38191
  · exact u38192

def r43072 : Route 9 := (fun mask => (mask,id))

def c43072 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43072 : Upper (D 6) (R 6) [34,136,80,260] 13 := by
  apply FastRouting.sound _ _ [34,136,80,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43072 c43072
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38193
  · exact u38194
  · exact u38195
  · exact u38196
  · exact u38197
  · exact u38198
  · exact u38199
  · exact u38200
  · exact u38201
  · exact u38202

def r43073 : Route 9 := (fun mask => (mask,id))

def c43073 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43073 : Upper (D 6) (R 6) [34,136,80,288] 13 := by
  apply FastRouting.sound _ _ [34,136,80,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43073 c43073
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38203
  · exact u38204
  · exact u38205
  · exact u38206
  · exact u38207
  · exact u38208

def r43074 : Route 9 := (fun mask => (mask,id))

def c43074 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43074 : Upper (D 6) (R 6) [34,136,80,320] 13 := by
  apply FastRouting.sound _ _ [34,136,80,320] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43074 c43074
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38209
  · exact u38210
  · exact u38211
  · exact u38212
  · exact u38213
  · exact u38214

def b43075 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 138 100 11 341 373 341 469 341), lower := (rows 35 138 100 11 16 32 64 128 256), losses := [] }

theorem u43075 : Upper (D 6) (R 6) [34,136,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43076 : Route 9 := (fun mask => (mask,id))

def c43076 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43076 : Upper (D 6) (R 6) [34,136,96,5] 13 := by
  apply FastRouting.sound _ _ [34,136,96,5] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43076 c43076
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38215
  · exact u38216
  · exact u38217
  · exact u38218
  · exact u38219
  · exact u38220
  · exact u38221
  · exact u38222
  · exact u38223
  · exact u38224

def r43077 : Route 9 := (fun mask => (mask,id))

def c43077 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43077 : Upper (D 6) (R 6) [34,136,96,6] 13 := by
  apply FastRouting.sound _ _ [34,136,96,6] 13 (by decide) (choices 2) [5,65,68,257,260,320] r43077 c43077
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38225
  · exact u38226
  · exact u38227
  · exact u38228
  · exact u38229
  · exact u38230

def r43078 : Route 9 := (fun mask => (mask,id))

def c43078 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43078 : Upper (D 6) (R 6) [34,136,96,17] 13 := by
  apply FastRouting.sound _ _ [34,136,96,17] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43078 c43078
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38231
  · exact u38232
  · exact u38233
  · exact u38234
  · exact u38235
  · exact u38236
  · exact u38237
  · exact u38238
  · exact u38239
  · exact u38240

def r43079 : Route 9 := (fun mask => (mask,id))

def c43079 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43079 : Upper (D 6) (R 6) [34,136,96,18] 13 := by
  apply FastRouting.sound _ _ [34,136,96,18] 13 (by decide) (choices 2) [5,65,68,257,260,320] r43079 c43079
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38241
  · exact u38242
  · exact u38243
  · exact u38244
  · exact u38245
  · exact u38246

#print axioms u43079
end Delivery.IrregularNine14.P06
