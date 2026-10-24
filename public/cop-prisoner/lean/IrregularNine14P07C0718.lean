import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0631
import IrregularNine14P07C0632
import IrregularNine14P07C0633
import IrregularNine14P07C0634
import IrregularNine14P07C0635

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m43080_3 : Upper (D 7) (R 7) [36,192,3,80,3] 13 :=
  permutation_upper _ _ _ [36,192,3,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37860

theorem m43080_9 : Upper (D 7) (R 7) [36,192,3,80,9] 13 :=
  permutation_upper _ _ _ [36,192,3,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37869

theorem m43080_10 : Upper (D 7) (R 7) [36,192,3,80,10] 13 :=
  permutation_upper _ _ _ [36,192,3,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37879

theorem m43080_33 : Upper (D 7) (R 7) [36,192,3,80,33] 13 :=
  permutation_upper _ _ _ [36,192,3,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37886

theorem m43080_34 : Upper (D 7) (R 7) [36,192,3,80,34] 13 :=
  permutation_upper _ _ _ [36,192,3,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37891

theorem m43080_40 : Upper (D 7) (R 7) [36,192,3,80,40] 13 :=
  permutation_upper _ _ _ [36,192,3,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37897

theorem m43080_129 : Upper (D 7) (R 7) [36,192,3,80,129] 13 :=
  permutation_upper _ _ _ [36,192,3,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37904

theorem m43080_130 : Upper (D 7) (R 7) [36,192,3,80,130] 13 :=
  permutation_upper _ _ _ [36,192,3,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37910

def r43080 : Route 9 := (fun mask => (mask,id))

def c43080 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43080 : Upper (D 7) (R 7) [36,192,3,80] 13 := by
  apply FastRouting.sound _ _ [36,192,3,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160,257,258,264,288,384] r43080 c43080
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43080_3
  · exact m43080_9
  · exact m43080_10
  · exact m43080_33
  · exact m43080_34
  · exact m43080_40
  · exact m43080_129
  · exact m43080_130
  · exact u37916
  · exact u37917
  · exact u37918
  · exact u37919
  · exact u37920
  · exact u37921
  · exact u37922

theorem m43081_3 : Upper (D 7) (R 7) [36,192,3,96,3] 13 :=
  permutation_upper _ _ _ [36,192,3,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37861

theorem m43081_9 : Upper (D 7) (R 7) [36,192,3,96,9] 13 :=
  permutation_upper _ _ _ [36,192,3,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37870

theorem m43081_10 : Upper (D 7) (R 7) [36,192,3,96,10] 13 :=
  permutation_upper _ _ _ [36,192,3,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37880

theorem m43081_129 : Upper (D 7) (R 7) [36,192,3,96,129] 13 :=
  permutation_upper _ _ _ [36,192,3,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37905

theorem m43081_130 : Upper (D 7) (R 7) [36,192,3,96,130] 13 :=
  permutation_upper _ _ _ [36,192,3,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37911

theorem m43081_136 : Upper (D 7) (R 7) [36,192,3,96,136] 13 :=
  permutation_upper _ _ _ [36,192,3,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37917

def r43081 : Route 9 := (fun mask => (mask,id))

def c43081 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43081 : Upper (D 7) (R 7) [36,192,3,96] 13 := by
  apply FastRouting.sound _ _ [36,192,3,96] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r43081 c43081
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43081_3
  · exact m43081_9
  · exact m43081_10
  · exact m43081_129
  · exact m43081_130
  · exact m43081_136
  · exact u37923
  · exact u37924
  · exact u37925
  · exact u37926

def b43082 : PairBound 9 := { available := 315, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 7 200 315 315 379 443 315), lower := (rows 37 194 7 200 16 32 64 128 256), losses := [] }

theorem u43082 : Upper (D 7) (R 7) [36,192,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43083_10 : Upper (D 7) (R 7) [36,192,3,257,10] 13 :=
  permutation_upper _ _ _ [36,192,3,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37882

theorem m43083_34 : Upper (D 7) (R 7) [36,192,3,257,34] 13 :=
  permutation_upper _ _ _ [36,192,3,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37892

theorem m43083_40 : Upper (D 7) (R 7) [36,192,3,257,40] 13 :=
  permutation_upper _ _ _ [36,192,3,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37899

theorem m43083_66 : Upper (D 7) (R 7) [36,192,3,257,66] 13 :=
  permutation_upper _ _ _ [36,192,3,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37912

theorem m43083_72 : Upper (D 7) (R 7) [36,192,3,257,72] 13 :=
  permutation_upper _ _ _ [36,192,3,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37918

theorem m43083_96 : Upper (D 7) (R 7) [36,192,3,257,96] 13 :=
  permutation_upper _ _ _ [36,192,3,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37923

theorem m43083_192 : Upper (D 7) (R 7) [36,192,3,257,192] 13 :=
  permutation_upper _ _ _ [36,192,3,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37927

def r43083 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43083 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43083 : Upper (D 7) (R 7) [36,192,3,257] 13 := by
  apply FastRouting.sound _ _ [36,192,3,257] 13 (by decide) (choices 2) [10,34,40,66,72,96,192] r43083 c43083
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43083_10
  · exact m43083_34
  · exact m43083_40
  · exact m43083_66
  · exact m43083_72
  · exact m43083_96
  · exact m43083_192

theorem m43084_9 : Upper (D 7) (R 7) [36,192,3,258,9] 13 :=
  permutation_upper _ _ _ [36,192,3,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37872

theorem m43084_33 : Upper (D 7) (R 7) [36,192,3,258,33] 13 :=
  permutation_upper _ _ _ [36,192,3,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37887

theorem m43084_40 : Upper (D 7) (R 7) [36,192,3,258,40] 13 :=
  permutation_upper _ _ _ [36,192,3,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37900

theorem m43084_65 : Upper (D 7) (R 7) [36,192,3,258,65] 13 :=
  permutation_upper _ _ _ [36,192,3,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37906

theorem m43084_72 : Upper (D 7) (R 7) [36,192,3,258,72] 13 :=
  permutation_upper _ _ _ [36,192,3,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37919

theorem m43084_96 : Upper (D 7) (R 7) [36,192,3,258,96] 13 :=
  permutation_upper _ _ _ [36,192,3,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37924

theorem m43084_192 : Upper (D 7) (R 7) [36,192,3,258,192] 13 :=
  permutation_upper _ _ _ [36,192,3,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37928

def r43084 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43084 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43084 : Upper (D 7) (R 7) [36,192,3,258] 13 := by
  apply FastRouting.sound _ _ [36,192,3,258] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r43084 c43084
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43084_9
  · exact m43084_33
  · exact m43084_40
  · exact m43084_65
  · exact m43084_72
  · exact m43084_96
  · exact m43084_192

theorem m43085_3 : Upper (D 7) (R 7) [36,192,3,272,3] 13 :=
  permutation_upper _ _ _ [36,192,3,3,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37862

theorem m43085_9 : Upper (D 7) (R 7) [36,192,3,272,9] 13 :=
  permutation_upper _ _ _ [36,192,3,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37873

theorem m43085_10 : Upper (D 7) (R 7) [36,192,3,272,10] 13 :=
  permutation_upper _ _ _ [36,192,3,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37883

theorem m43085_33 : Upper (D 7) (R 7) [36,192,3,272,33] 13 :=
  permutation_upper _ _ _ [36,192,3,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37888

theorem m43085_34 : Upper (D 7) (R 7) [36,192,3,272,34] 13 :=
  permutation_upper _ _ _ [36,192,3,34,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37893

theorem m43085_40 : Upper (D 7) (R 7) [36,192,3,272,40] 13 :=
  permutation_upper _ _ _ [36,192,3,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37901

theorem m43085_65 : Upper (D 7) (R 7) [36,192,3,272,65] 13 :=
  permutation_upper _ _ _ [36,192,3,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37907

theorem m43085_66 : Upper (D 7) (R 7) [36,192,3,272,66] 13 :=
  permutation_upper _ _ _ [36,192,3,66,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37913

theorem m43085_72 : Upper (D 7) (R 7) [36,192,3,272,72] 13 :=
  permutation_upper _ _ _ [36,192,3,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37920

theorem m43085_96 : Upper (D 7) (R 7) [36,192,3,272,96] 13 :=
  permutation_upper _ _ _ [36,192,3,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37925

theorem m43085_192 : Upper (D 7) (R 7) [36,192,3,272,192] 13 :=
  permutation_upper _ _ _ [36,192,3,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37929

def r43085 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43085 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43085 : Upper (D 7) (R 7) [36,192,3,272] 13 := by
  apply FastRouting.sound _ _ [36,192,3,272] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,192] r43085 c43085
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43085_3
  · exact m43085_9
  · exact m43085_10
  · exact m43085_33
  · exact m43085_34
  · exact m43085_40
  · exact m43085_65
  · exact m43085_66
  · exact m43085_72
  · exact m43085_96
  · exact m43085_192

theorem m43086_3 : Upper (D 7) (R 7) [36,192,3,288,3] 13 :=
  permutation_upper _ _ _ [36,192,3,3,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37863

theorem m43086_9 : Upper (D 7) (R 7) [36,192,3,288,9] 13 :=
  permutation_upper _ _ _ [36,192,3,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37874

theorem m43086_10 : Upper (D 7) (R 7) [36,192,3,288,10] 13 :=
  permutation_upper _ _ _ [36,192,3,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37884

theorem m43086_65 : Upper (D 7) (R 7) [36,192,3,288,65] 13 :=
  permutation_upper _ _ _ [36,192,3,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37908

theorem m43086_66 : Upper (D 7) (R 7) [36,192,3,288,66] 13 :=
  permutation_upper _ _ _ [36,192,3,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37914

theorem m43086_72 : Upper (D 7) (R 7) [36,192,3,288,72] 13 :=
  permutation_upper _ _ _ [36,192,3,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37921

theorem m43086_192 : Upper (D 7) (R 7) [36,192,3,288,192] 13 :=
  permutation_upper _ _ _ [36,192,3,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37930

def r43086 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43086 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43086 : Upper (D 7) (R 7) [36,192,3,288] 13 := by
  apply FastRouting.sound _ _ [36,192,3,288] 13 (by decide) (choices 2) [3,9,10,65,66,72,192] r43086 c43086
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43086_3
  · exact m43086_9
  · exact m43086_10
  · exact m43086_65
  · exact m43086_66
  · exact m43086_72
  · exact m43086_192

theorem m43087_3 : Upper (D 7) (R 7) [36,192,3,320,3] 13 :=
  permutation_upper _ _ _ [36,192,3,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37864

theorem m43087_9 : Upper (D 7) (R 7) [36,192,3,320,9] 13 :=
  permutation_upper _ _ _ [36,192,3,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37875

theorem m43087_10 : Upper (D 7) (R 7) [36,192,3,320,10] 13 :=
  permutation_upper _ _ _ [36,192,3,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37885

theorem m43087_33 : Upper (D 7) (R 7) [36,192,3,320,33] 13 :=
  permutation_upper _ _ _ [36,192,3,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37889

theorem m43087_34 : Upper (D 7) (R 7) [36,192,3,320,34] 13 :=
  permutation_upper _ _ _ [36,192,3,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37894

theorem m43087_40 : Upper (D 7) (R 7) [36,192,3,320,40] 13 :=
  permutation_upper _ _ _ [36,192,3,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37902

theorem m43087_129 : Upper (D 7) (R 7) [36,192,3,320,129] 13 :=
  permutation_upper _ _ _ [36,192,3,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37909

theorem m43087_130 : Upper (D 7) (R 7) [36,192,3,320,130] 13 :=
  permutation_upper _ _ _ [36,192,3,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37915

theorem m43087_136 : Upper (D 7) (R 7) [36,192,3,320,136] 13 :=
  permutation_upper _ _ _ [36,192,3,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37922

theorem m43087_160 : Upper (D 7) (R 7) [36,192,3,320,160] 13 :=
  permutation_upper _ _ _ [36,192,3,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37926

def r43087 : Route 9 := (fun mask => (mask,id))

def c43087 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43087 : Upper (D 7) (R 7) [36,192,3,320] 13 := by
  apply FastRouting.sound _ _ [36,192,3,320] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43087 c43087
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43087_3
  · exact m43087_9
  · exact m43087_10
  · exact m43087_33
  · exact m43087_34
  · exact m43087_40
  · exact m43087_129
  · exact m43087_130
  · exact m43087_136
  · exact m43087_160

def b43088 : PairBound 9 := { available := 498, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 194 13 11 498 498 498 498 498), lower := (rows 37 194 13 11 16 32 64 128 256), losses := [] }

theorem u43088 : Upper (D 7) (R 7) [36,192,9,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43089 : PairBound 9 := { available := 482, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 194 13 25 498 482 482 482 482), lower := (rows 37 194 13 25 16 32 64 128 256), losses := [] }

theorem u43089 : Upper (D 7) (R 7) [36,192,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43090 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43090 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u43090 : Upper (D 7) (R 7) [36,192,9,18] 13 := by
  apply FastRouting.sound _ _ [36,192,9,18] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r43090 c43090
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37931
  · exact u37932
  · exact u37933
  · exact u37934
  · exact u37935
  · exact u37936
  · exact u37937
  · exact u37938
  · exact u37939
  · exact u37940
  · exact u37941

def b43091 : PairBound 9 := { available := 466, camps := [{ cop := 5, region := 13, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 41 466 498 466 466 466), lower := (rows 37 194 13 41 16 32 64 128 256), losses := [] }

theorem u43091 : Upper (D 7) (R 7) [36,192,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43092 : PairBound 9 := { available := 467, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 42 467 499 467 467 467), lower := (rows 37 194 13 42 16 32 64 128 256), losses := [] }

theorem u43092 : Upper (D 7) (R 7) [36,192,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43093 : PairBound 9 := { available := 451, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 56 467 483 451 451 451), lower := (rows 37 194 13 56 16 32 64 128 256), losses := [] }

theorem u43093 : Upper (D 7) (R 7) [36,192,9,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43094 : PairBound 9 := { available := 434, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 194 13 73 434 434 498 434 434), lower := (rows 37 194 13 73 16 32 64 128 256), losses := [] }

theorem u43094 : Upper (D 7) (R 7) [36,192,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43095 : PairBound 9 := { available := 435, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 194 13 74 435 435 499 435 435), lower := (rows 37 194 13 74 16 32 64 128 256), losses := [] }

theorem u43095 : Upper (D 7) (R 7) [36,192,9,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43096 : Route 9 := (fun mask => (mask,id))

def c43096 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43096 : Upper (D 7) (R 7) [36,192,9,80] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r43096 c43096
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37942
  · exact u37943
  · exact u37944
  · exact u37945
  · exact u37946
  · exact u37947
  · exact u37948
  · exact u37949
  · exact u37950
  · exact u37951

def b43097 : PairBound 9 := { available := 403, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 104 403 435 467 403 403), lower := (rows 37 194 13 104 16 32 64 128 256), losses := [] }

theorem u43097 : Upper (D 7) (R 7) [36,192,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43098 : PairBound 9 := { available := 307, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 13 200 307 307 371 435 307), lower := (rows 37 194 13 200 16 32 64 128 256), losses := [] }

theorem u43098 : Upper (D 7) (R 7) [36,192,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43099 : PairBound 9 := { available := 242, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 194 13 265 242 242 242 242 498), lower := (rows 37 194 13 265 16 32 64 128 256), losses := [] }

theorem u43099 : Upper (D 7) (R 7) [36,192,9,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43100 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43100 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43100 : Upper (D 7) (R 7) [36,192,9,258] 13 := by
  apply FastRouting.sound _ _ [36,192,9,258] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r43100 c43100
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37952
  · exact u37953
  · exact u37954
  · exact u37955
  · exact u37956
  · exact u37957
  · exact u37958

def r43101 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43101 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43101 : Upper (D 7) (R 7) [36,192,9,272] 13 := by
  apply FastRouting.sound _ _ [36,192,9,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r43101 c43101
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37959
  · exact u37960
  · exact u37961
  · exact u37962
  · exact u37963
  · exact u37964
  · exact u37965

def b43102 : PairBound 9 := { available := 211, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 296 211 243 211 211 467), lower := (rows 37 194 13 296 16 32 64 128 256), losses := [] }

theorem u43102 : Upper (D 7) (R 7) [36,192,9,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43103 : Route 9 := (fun mask => (mask,id))

def c43103 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43103 : Upper (D 7) (R 7) [36,192,9,320] 13 := by
  apply FastRouting.sound _ _ [36,192,9,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43103 c43103
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37966
  · exact u37967
  · exact u37968
  · exact u37969
  · exact u37970
  · exact u37971

def b43104 : PairBound 9 := { available := 497, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 194 14 11 497 497 497 497 497), lower := (rows 37 194 14 11 16 32 64 128 256), losses := [] }

theorem u43104 : Upper (D 7) (R 7) [36,192,10,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43105 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43105 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u43105 : Upper (D 7) (R 7) [36,192,10,17] 13 := by
  apply FastRouting.sound _ _ [36,192,10,17] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r43105 c43105
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37972
  · exact u37973
  · exact u37974
  · exact u37975
  · exact u37976
  · exact u37977
  · exact u37978
  · exact u37979
  · exact u37980
  · exact u37981
  · exact u37982

def b43106 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 194 14 26 497 481 481 481 481), lower := (rows 37 194 14 26 16 32 64 128 256), losses := [] }

theorem u43106 : Upper (D 7) (R 7) [36,192,10,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43107 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 14 41 467 499 467 467 467), lower := (rows 37 194 14 41 16 32 64 128 256), losses := [] }

theorem u43107 : Upper (D 7) (R 7) [36,192,10,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43108 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 14 42 465 497 465 465 465), lower := (rows 37 194 14 42 16 32 64 128 256), losses := [] }

theorem u43108 : Upper (D 7) (R 7) [36,192,10,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43109 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43109 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43109 : Upper (D 7) (R 7) [36,192,10,48] 13 := by
  apply FastRouting.sound _ _ [36,192,10,48] 13 (by decide) (choices 2) [3,65,66,192,257,258,320] r43109 c43109
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37983
  · exact u37984
  · exact u37985
  · exact u37986
  · exact u37987
  · exact u37988
  · exact u37989

def r43110 : Route 9 := (fun mask => (mask,id))

def c43110 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43110 : Upper (D 7) (R 7) [36,192,10,65] 13 := by
  apply FastRouting.sound _ _ [36,192,10,65] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r43110 c43110
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37990
  · exact u37991
  · exact u37992
  · exact u37993
  · exact u37994
  · exact u37995
  · exact u37996
  · exact u37997
  · exact u37998
  · exact u37999

def b43111 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(3,0)], upper := (rows 37 194 14 74 433 433 497 433 433), lower := (rows 37 194 14 74 16 32 64 128 256), losses := [] }

theorem u43111 : Upper (D 7) (R 7) [36,192,10,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43112 : Route 9 := (fun mask => (mask,id))

def c43112 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43112 : Upper (D 7) (R 7) [36,192,10,80] 13 := by
  apply FastRouting.sound _ _ [36,192,10,80] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r43112 c43112
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38000
  · exact u38001
  · exact u38002
  · exact u38003
  · exact u38004
  · exact u38005
  · exact u38006
  · exact u38007
  · exact u38008
  · exact u38009

def b43113 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(1,5),(4,5),(4,6)], upper := (rows 37 194 14 104 403 435 467 403 403), lower := (rows 37 194 14 104 16 32 64 128 256), losses := [] }

theorem u43113 : Upper (D 7) (R 7) [36,192,10,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43114 : PairBound 9 := { available := 307, camps := [{ cop := 1, region := 12, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 194 14 200 307 307 371 435 307), lower := (rows 37 194 14 200 16 32 64 128 256), losses := [] }

theorem u43114 : Upper (D 7) (R 7) [36,192,10,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43115 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43115 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43115 : Upper (D 7) (R 7) [36,192,10,257] 13 := by
  apply FastRouting.sound _ _ [36,192,10,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r43115 c43115
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38010
  · exact u38011
  · exact u38012
  · exact u38013
  · exact u38014
  · exact u38015
  · exact u38016

def b43116 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 194 14 266 241 241 241 241 497), lower := (rows 37 194 14 266 16 32 64 128 256), losses := [] }

theorem u43116 : Upper (D 7) (R 7) [36,192,10,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43117 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43117 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43117 : Upper (D 7) (R 7) [36,192,10,272] 13 := by
  apply FastRouting.sound _ _ [36,192,10,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r43117 c43117
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38017
  · exact u38018
  · exact u38019
  · exact u38020
  · exact u38021
  · exact u38022
  · exact u38023

def r43118 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43118 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43118 : Upper (D 7) (R 7) [36,192,10,288] 13 := by
  apply FastRouting.sound _ _ [36,192,10,288] 13 (by decide) (choices 2) [3,65,66,192] r43118 c43118
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u38024
  · exact u38025
  · exact u38026
  · exact u38027

def r43119 : Route 9 := (fun mask => (mask,id))

def c43119 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43119 : Upper (D 7) (R 7) [36,192,10,320] 13 := by
  apply FastRouting.sound _ _ [36,192,10,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43119 c43119
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38028
  · exact u38029
  · exact u38030
  · exact u38031
  · exact u38032
  · exact u38033

def r43120 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43120 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u43120 : Upper (D 7) (R 7) [36,192,24,3] 13 := by
  apply FastRouting.sound _ _ [36,192,24,3] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r43120 c43120
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38034
  · exact u38035
  · exact u38036
  · exact u38037
  · exact u38038
  · exact u38039
  · exact u38040
  · exact u38041
  · exact u38042
  · exact u38043
  · exact u38044

def b43121 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 28 41 467 483 451 451 451), lower := (rows 37 194 28 41 16 32 64 128 256), losses := [] }

theorem u43121 : Upper (D 7) (R 7) [36,192,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43122_3 : Upper (D 7) (R 7) [36,192,24,34,3] 13 :=
  permutation_upper _ _ _ [36,192,24,3,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38036

def r43122 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43122 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43122 : Upper (D 7) (R 7) [36,192,24,34] 13 := by
  apply FastRouting.sound _ _ [36,192,24,34] 13 (by decide) (choices 2) [3,65,66,192,257,258,320] r43122 c43122
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43122_3
  · exact u38049
  · exact u38050
  · exact u38051
  · exact u38052
  · exact u38053
  · exact u38054

theorem m43123_3 : Upper (D 7) (R 7) [36,192,24,65,3] 13 :=
  permutation_upper _ _ _ [36,192,24,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38037

theorem m43123_33 : Upper (D 7) (R 7) [36,192,24,65,33] 13 :=
  permutation_upper _ _ _ [36,192,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38045

theorem m43123_34 : Upper (D 7) (R 7) [36,192,24,65,34] 13 :=
  permutation_upper _ _ _ [36,192,24,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38049

def r43123 : Route 9 := (fun mask => (mask,id))

def c43123 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43123 : Upper (D 7) (R 7) [36,192,24,65] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r43123 c43123
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43123_3
  · exact m43123_33
  · exact m43123_34
  · exact u38055
  · exact u38056
  · exact u38057
  · exact u38058
  · exact u38059
  · exact u38060
  · exact u38061

def b43124 : PairBound 9 := { available := 419, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 194 28 74 435 419 483 419 419), lower := (rows 37 194 28 74 16 32 64 128 256), losses := [] }

theorem u43124 : Upper (D 7) (R 7) [36,192,24,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43125_3 : Upper (D 7) (R 7) [36,192,24,96,3] 13 :=
  permutation_upper _ _ _ [36,192,24,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38039

theorem m43125_129 : Upper (D 7) (R 7) [36,192,24,96,129] 13 :=
  permutation_upper _ _ _ [36,192,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38057

theorem m43125_130 : Upper (D 7) (R 7) [36,192,24,96,130] 13 :=
  permutation_upper _ _ _ [36,192,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38062

def r43125 : Route 9 := (fun mask => (mask,id))

def c43125 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43125 : Upper (D 7) (R 7) [36,192,24,96] 13 := by
  apply FastRouting.sound _ _ [36,192,24,96] 13 (by decide) (choices 2) [3,129,130,257,258,384] r43125 c43125
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43125_3
  · exact m43125_129
  · exact m43125_130
  · exact u38067
  · exact u38068
  · exact u38069

def b43126 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 28 200 307 291 355 419 291), lower := (rows 37 194 28 200 16 32 64 128 256), losses := [] }

theorem u43126 : Upper (D 7) (R 7) [36,192,24,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43127_3 : Upper (D 7) (R 7) [36,192,24,257,3] 13 :=
  permutation_upper _ _ _ [36,192,24,3,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38041

theorem m43127_33 : Upper (D 7) (R 7) [36,192,24,257,33] 13 :=
  permutation_upper _ _ _ [36,192,24,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38046

theorem m43127_34 : Upper (D 7) (R 7) [36,192,24,257,34] 13 :=
  permutation_upper _ _ _ [36,192,24,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38052

theorem m43127_65 : Upper (D 7) (R 7) [36,192,24,257,65] 13 :=
  permutation_upper _ _ _ [36,192,24,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38058

theorem m43127_66 : Upper (D 7) (R 7) [36,192,24,257,66] 13 :=
  permutation_upper _ _ _ [36,192,24,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38063

theorem m43127_96 : Upper (D 7) (R 7) [36,192,24,257,96] 13 :=
  permutation_upper _ _ _ [36,192,24,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38067

theorem m43127_192 : Upper (D 7) (R 7) [36,192,24,257,192] 13 :=
  permutation_upper _ _ _ [36,192,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38070

def r43127 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43127 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43127 : Upper (D 7) (R 7) [36,192,24,257] 13 := by
  apply FastRouting.sound _ _ [36,192,24,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r43127 c43127
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43127_3
  · exact m43127_33
  · exact m43127_34
  · exact m43127_65
  · exact m43127_66
  · exact m43127_96
  · exact m43127_192

theorem m43128_3 : Upper (D 7) (R 7) [36,192,24,258,3] 13 :=
  permutation_upper _ _ _ [36,192,24,3,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38042

theorem m43128_33 : Upper (D 7) (R 7) [36,192,24,258,33] 13 :=
  permutation_upper _ _ _ [36,192,24,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38047

theorem m43128_34 : Upper (D 7) (R 7) [36,192,24,258,34] 13 :=
  permutation_upper _ _ _ [36,192,24,34,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38053

theorem m43128_65 : Upper (D 7) (R 7) [36,192,24,258,65] 13 :=
  permutation_upper _ _ _ [36,192,24,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38059

theorem m43128_66 : Upper (D 7) (R 7) [36,192,24,258,66] 13 :=
  permutation_upper _ _ _ [36,192,24,66,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38064

theorem m43128_96 : Upper (D 7) (R 7) [36,192,24,258,96] 13 :=
  permutation_upper _ _ _ [36,192,24,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38068

theorem m43128_192 : Upper (D 7) (R 7) [36,192,24,258,192] 13 :=
  permutation_upper _ _ _ [36,192,24,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38071

def r43128 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43128 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43128 : Upper (D 7) (R 7) [36,192,24,258] 13 := by
  apply FastRouting.sound _ _ [36,192,24,258] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r43128 c43128
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43128_3
  · exact m43128_33
  · exact m43128_34
  · exact m43128_65
  · exact m43128_66
  · exact m43128_96
  · exact m43128_192

theorem m43129_3 : Upper (D 7) (R 7) [36,192,24,288,3] 13 :=
  permutation_upper _ _ _ [36,192,24,3,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38043

theorem m43129_65 : Upper (D 7) (R 7) [36,192,24,288,65] 13 :=
  permutation_upper _ _ _ [36,192,24,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38060

theorem m43129_66 : Upper (D 7) (R 7) [36,192,24,288,66] 13 :=
  permutation_upper _ _ _ [36,192,24,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38065

theorem m43129_192 : Upper (D 7) (R 7) [36,192,24,288,192] 13 :=
  permutation_upper _ _ _ [36,192,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38072

def r43129 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43129 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43129 : Upper (D 7) (R 7) [36,192,24,288] 13 := by
  apply FastRouting.sound _ _ [36,192,24,288] 13 (by decide) (choices 2) [3,65,66,192] r43129 c43129
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m43129_3
  · exact m43129_65
  · exact m43129_66
  · exact m43129_192

theorem m43130_3 : Upper (D 7) (R 7) [36,192,24,320,3] 13 :=
  permutation_upper _ _ _ [36,192,24,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38044

theorem m43130_33 : Upper (D 7) (R 7) [36,192,24,320,33] 13 :=
  permutation_upper _ _ _ [36,192,24,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38048

theorem m43130_34 : Upper (D 7) (R 7) [36,192,24,320,34] 13 :=
  permutation_upper _ _ _ [36,192,24,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38054

theorem m43130_129 : Upper (D 7) (R 7) [36,192,24,320,129] 13 :=
  permutation_upper _ _ _ [36,192,24,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38061

theorem m43130_130 : Upper (D 7) (R 7) [36,192,24,320,130] 13 :=
  permutation_upper _ _ _ [36,192,24,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38066

theorem m43130_160 : Upper (D 7) (R 7) [36,192,24,320,160] 13 :=
  permutation_upper _ _ _ [36,192,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38069

def r43130 : Route 9 := (fun mask => (mask,id))

def c43130 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43130 : Upper (D 7) (R 7) [36,192,24,320] 13 := by
  apply FastRouting.sound _ _ [36,192,24,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43130 c43130
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43130_3
  · exact m43130_33
  · exact m43130_34
  · exact m43130_129
  · exact m43130_130
  · exact m43130_160

def r43131 : Route 9 := (fun mask => (mask,id))

def c43131 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43131 : Upper (D 7) (R 7) [36,192,65,3] 13 := by
  apply FastRouting.sound _ _ [36,192,65,3] 13 (by decide) (choices 2) [10,34,40,130,136,160,258,264,288,384] r43131 c43131
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38073
  · exact u38074
  · exact u38075
  · exact u38076
  · exact u38077
  · exact u38078
  · exact u38079
  · exact u38080
  · exact u38081
  · exact u38082

def r43132 : Route 9 := (fun mask => (mask,id))

def c43132 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43132 : Upper (D 7) (R 7) [36,192,65,17] 13 := by
  apply FastRouting.sound _ _ [36,192,65,17] 13 (by decide) (choices 2) [10,34,40,130,136,160,258,264,288,384] r43132 c43132
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38083
  · exact u38084
  · exact u38085
  · exact u38086
  · exact u38087
  · exact u38088
  · exact u38089
  · exact u38090
  · exact u38091
  · exact u38092

theorem m43133_3 : Upper (D 7) (R 7) [36,192,65,18,3] 13 :=
  permutation_upper _ _ _ [36,192,65,3,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38073

theorem m43133_9 : Upper (D 7) (R 7) [36,192,65,18,9] 13 :=
  permutation_upper _ _ _ [36,192,65,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38083

def r43133 : Route 9 := (fun mask => (mask,id))

def c43133 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43133 : Upper (D 7) (R 7) [36,192,65,18] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160,257,258,264,288,384] r43133 c43133
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43133_3
  · exact m43133_9
  · exact u38093
  · exact u38094
  · exact u38095
  · exact u38096
  · exact u38097
  · exact u38098
  · exact u38099
  · exact u38100
  · exact u38101
  · exact u38102
  · exact u38103
  · exact u38104
  · exact u38105

def b43134 : PairBound 9 := { available := 410, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 69 41 410 442 474 410 410), lower := (rows 37 194 69 41 16 32 64 128 256), losses := [] }

theorem u43134 : Upper (D 7) (R 7) [36,192,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43135_3 : Upper (D 7) (R 7) [36,192,65,34,3] 13 :=
  permutation_upper _ _ _ [36,192,65,3,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38074

theorem m43135_9 : Upper (D 7) (R 7) [36,192,65,34,9] 13 :=
  permutation_upper _ _ _ [36,192,65,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38084

theorem m43135_10 : Upper (D 7) (R 7) [36,192,65,34,10] 13 :=
  permutation_upper _ _ _ [36,192,65,18,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38095

def r43135 : Route 9 := (fun mask => (mask,id))

def c43135 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43135 : Upper (D 7) (R 7) [36,192,65,34] 13 := by
  apply FastRouting.sound _ _ [36,192,65,34] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r43135 c43135
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43135_3
  · exact m43135_9
  · exact m43135_10
  · exact u38110
  · exact u38111
  · exact u38112
  · exact u38113
  · exact u38114
  · exact u38115
  · exact u38116

theorem m43136_3 : Upper (D 7) (R 7) [36,192,65,48,3] 13 :=
  permutation_upper _ _ _ [36,192,65,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38075

theorem m43136_9 : Upper (D 7) (R 7) [36,192,65,48,9] 13 :=
  permutation_upper _ _ _ [36,192,65,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38085

theorem m43136_10 : Upper (D 7) (R 7) [36,192,65,48,10] 13 :=
  permutation_upper _ _ _ [36,192,65,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38096

def r43136 : Route 9 := (fun mask => (mask,id))

def c43136 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43136 : Upper (D 7) (R 7) [36,192,65,48] 13 := by
  apply FastRouting.sound _ _ [36,192,65,48] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r43136 c43136
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43136_3
  · exact m43136_9
  · exact m43136_10
  · exact u38117
  · exact u38118
  · exact u38119
  · exact u38120
  · exact u38121
  · exact u38122
  · exact u38123

theorem m43137_10 : Upper (D 7) (R 7) [36,192,65,129,10] 13 :=
  permutation_upper _ _ _ [36,192,65,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38097

theorem m43137_34 : Upper (D 7) (R 7) [36,192,65,129,34] 13 :=
  permutation_upper _ _ _ [36,192,65,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38110

theorem m43137_40 : Upper (D 7) (R 7) [36,192,65,129,40] 13 :=
  permutation_upper _ _ _ [36,192,65,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38117

def r43137 : Route 9 := (fun mask => (mask,id))

def c43137 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43137 : Upper (D 7) (R 7) [36,192,65,129] 13 := by
  apply FastRouting.sound _ _ [36,192,65,129] 13 (by decide) (choices 2) [10,34,40,258,264,288] r43137 c43137
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43137_10
  · exact m43137_34
  · exact m43137_40
  · exact u38124
  · exact u38125
  · exact u38126

def b43138 : PairBound 9 := { available := 315, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 37 194 69 138 315 315 379 443 315), lower := (rows 37 194 69 138 16 32 64 128 256), losses := [] }

theorem u43138 : Upper (D 7) (R 7) [36,192,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43139_3 : Upper (D 7) (R 7) [36,192,65,144,3] 13 :=
  permutation_upper _ _ _ [36,192,65,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38077

theorem m43139_9 : Upper (D 7) (R 7) [36,192,65,144,9] 13 :=
  permutation_upper _ _ _ [36,192,65,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38087

theorem m43139_10 : Upper (D 7) (R 7) [36,192,65,144,10] 13 :=
  permutation_upper _ _ _ [36,192,65,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38099

theorem m43139_33 : Upper (D 7) (R 7) [36,192,65,144,33] 13 :=
  permutation_upper _ _ _ [36,192,65,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38106

theorem m43139_34 : Upper (D 7) (R 7) [36,192,65,144,34] 13 :=
  permutation_upper _ _ _ [36,192,65,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38112

theorem m43139_40 : Upper (D 7) (R 7) [36,192,65,144,40] 13 :=
  permutation_upper _ _ _ [36,192,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38119

def r43139 : Route 9 := (fun mask => (mask,id))

def c43139 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43139 : Upper (D 7) (R 7) [36,192,65,144] 13 := by
  apply FastRouting.sound _ _ [36,192,65,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r43139 c43139
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43139_3
  · exact m43139_9
  · exact m43139_10
  · exact m43139_33
  · exact m43139_34
  · exact m43139_40
  · exact u38131
  · exact u38132
  · exact u38133
  · exact u38134

#print axioms u43139
end Delivery.IrregularNine14.P07
