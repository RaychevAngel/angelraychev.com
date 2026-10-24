import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0496
import IrregularNine14P06C0497
import IrregularNine14P06C0498
import IrregularNine14P06C0499
import IrregularNine14P06C0500

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m41100_3 : Upper (D 6) (R 6) [6,160,320,17,3] 13 :=
  permutation_upper _ _ _ [6,160,320,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29778

theorem m41100_5 : Upper (D 6) (R 6) [6,160,320,17,5] 13 :=
  permutation_upper _ _ _ [6,160,320,3,9] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29778

theorem m41100_6 : Upper (D 6) (R 6) [6,160,320,17,6] 13 :=
  permutation_upper _ _ _ [6,160,320,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29786

theorem m41100_12 : Upper (D 6) (R 6) [6,160,320,17,12] 13 :=
  permutation_upper _ _ _ [6,160,320,17,10] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29791

theorem m41100_65 : Upper (D 6) (R 6) [6,160,320,17,65] 13 :=
  permutation_upper _ _ _ [6,160,320,17,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29792

theorem m41100_66 : Upper (D 6) (R 6) [6,160,320,17,66] 13 :=
  permutation_upper _ _ _ [6,160,320,17,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29794

theorem m41100_68 : Upper (D 6) (R 6) [6,160,320,17,68] 13 :=
  permutation_upper _ _ _ [6,160,320,17,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29793

theorem m41100_72 : Upper (D 6) (R 6) [6,160,320,17,72] 13 :=
  permutation_upper _ _ _ [6,160,320,17,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29795

def r41100 : Route 9 := (fun mask => (mask,id))

def c41100 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41100 : Upper (D 6) (R 6) [6,160,320,17] 13 := by
  apply FastRouting.sound _ _ [6,160,320,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r41100 c41100
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41100_3
  · exact m41100_5
  · exact m41100_6
  · exact u29790
  · exact u29791
  · exact m41100_12
  · exact u29792
  · exact u29793
  · exact u29794
  · exact u29795
  · exact m41100_65
  · exact m41100_66
  · exact m41100_68
  · exact m41100_72
  · exact u29796

theorem m41101_5 : Upper (D 6) (R 6) [6,160,320,18,5] 13 :=
  permutation_upper _ _ _ [6,160,320,3,12] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29779

theorem m41101_9 : Upper (D 6) (R 6) [6,160,320,18,9] 13 :=
  permutation_upper _ _ _ [6,160,320,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29791

def r41101 : Route 9 := (fun mask => (mask,id))

def c41101 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41101 : Upper (D 6) (R 6) [6,160,320,18] 13 := by
  apply FastRouting.sound _ _ [6,160,320,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r41101 c41101
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41101_5
  · exact m41101_9
  · exact u29797
  · exact u29798
  · exact u29799
  · exact u29800
  · exact u29801
  · exact u29802
  · exact u29803
  · exact u29804

theorem m41102_3 : Upper (D 6) (R 6) [6,160,320,33,3] 13 :=
  permutation_upper _ _ _ [6,160,320,3,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29780

theorem m41102_5 : Upper (D 6) (R 6) [6,160,320,33,5] 13 :=
  permutation_upper _ _ _ [6,160,320,3,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29783

theorem m41102_6 : Upper (D 6) (R 6) [6,160,320,33,6] 13 :=
  permutation_upper _ _ _ [6,160,320,6,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29787

theorem m41102_9 : Upper (D 6) (R 6) [6,160,320,33,9] 13 :=
  permutation_upper _ _ _ [6,160,320,17,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29792

theorem m41102_10 : Upper (D 6) (R 6) [6,160,320,33,10] 13 :=
  permutation_upper _ _ _ [6,160,320,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29798

theorem m41102_12 : Upper (D 6) (R 6) [6,160,320,33,12] 13 :=
  permutation_upper _ _ _ [6,160,320,18,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29801

def r41102 : Route 9 := (fun mask => (mask,id))

def c41102 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41102 : Upper (D 6) (R 6) [6,160,320,33] 13 := by
  apply FastRouting.sound _ _ [6,160,320,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r41102 c41102
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41102_3
  · exact m41102_5
  · exact m41102_6
  · exact m41102_9
  · exact m41102_10
  · exact m41102_12
  · exact u29805
  · exact u29806
  · exact u29807
  · exact u29808

def b41103 : PairBound 9 := { available := 93, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 162 324 42 93 125 93 221 349), lower := (rows 7 162 324 42 16 32 64 128 256), losses := [] }

theorem u41103 : Upper (D 6) (R 6) [6,160,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41104_3 : Upper (D 6) (R 6) [6,160,320,36,3] 13 :=
  permutation_upper _ _ _ [6,160,320,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29781

theorem m41104_9 : Upper (D 6) (R 6) [6,160,320,36,9] 13 :=
  permutation_upper _ _ _ [6,160,320,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29794

theorem m41104_10 : Upper (D 6) (R 6) [6,160,320,36,10] 13 :=
  permutation_upper _ _ _ [6,160,320,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29799

theorem m41104_65 : Upper (D 6) (R 6) [6,160,320,36,65] 13 :=
  permutation_upper _ _ _ [6,160,320,33,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29806

def r41104 : Route 9 := (fun mask => (mask,id))

def c41104 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41104 : Upper (D 6) (R 6) [6,160,320,36] 13 := by
  apply FastRouting.sound _ _ [6,160,320,36] 13 (by decide) (choices 2) [3,9,10,65,66,72] r41104 c41104
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41104_3
  · exact m41104_9
  · exact m41104_10
  · exact m41104_65
  · exact u29810
  · exact u29811

theorem m41105_3 : Upper (D 6) (R 6) [6,160,320,48,3] 13 :=
  permutation_upper _ _ _ [6,160,320,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29782

theorem m41105_5 : Upper (D 6) (R 6) [6,160,320,48,5] 13 :=
  permutation_upper _ _ _ [6,160,320,3,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29784

theorem m41105_6 : Upper (D 6) (R 6) [6,160,320,48,6] 13 :=
  permutation_upper _ _ _ [6,160,320,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29788

theorem m41105_9 : Upper (D 6) (R 6) [6,160,320,48,9] 13 :=
  permutation_upper _ _ _ [6,160,320,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29795

theorem m41105_10 : Upper (D 6) (R 6) [6,160,320,48,10] 13 :=
  permutation_upper _ _ _ [6,160,320,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29800

theorem m41105_12 : Upper (D 6) (R 6) [6,160,320,48,12] 13 :=
  permutation_upper _ _ _ [6,160,320,18,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29803

theorem m41105_65 : Upper (D 6) (R 6) [6,160,320,48,65] 13 :=
  permutation_upper _ _ _ [6,160,320,33,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29808

theorem m41105_66 : Upper (D 6) (R 6) [6,160,320,48,66] 13 :=
  permutation_upper _ _ _ [6,160,320,36,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29811

theorem m41105_68 : Upper (D 6) (R 6) [6,160,320,48,68] 13 :=
  permutation_upper _ _ _ [6,160,320,34,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29809

def r41105 : Route 9 := (fun mask => (mask,id))

def c41105 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41105 : Upper (D 6) (R 6) [6,160,320,48] 13 := by
  apply FastRouting.sound _ _ [6,160,320,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r41105 c41105
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41105_3
  · exact m41105_5
  · exact m41105_6
  · exact m41105_9
  · exact m41105_10
  · exact m41105_12
  · exact m41105_65
  · exact m41105_66
  · exact m41105_68
  · exact u29812

theorem m41106_3 : Upper (D 6) (R 6) [6,160,320,96,3] 13 :=
  permutation_upper _ _ _ [6,160,320,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29785

theorem m41106_5 : Upper (D 6) (R 6) [6,160,320,96,5] 13 :=
  permutation_upper _ _ _ [6,160,320,3,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29785

theorem m41106_6 : Upper (D 6) (R 6) [6,160,320,96,6] 13 :=
  permutation_upper _ _ _ [6,160,320,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29789

theorem m41106_9 : Upper (D 6) (R 6) [6,160,320,96,9] 13 :=
  permutation_upper _ _ _ [6,160,320,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29796

theorem m41106_10 : Upper (D 6) (R 6) [6,160,320,96,10] 13 :=
  permutation_upper _ _ _ [6,160,320,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29804

theorem m41106_12 : Upper (D 6) (R 6) [6,160,320,96,12] 13 :=
  permutation_upper _ _ _ [6,160,320,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29804

def r41106 : Route 9 := (fun mask => (mask,id))

def c41106 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41106 : Upper (D 6) (R 6) [6,160,320,96] 13 := by
  apply FastRouting.sound _ _ [6,160,320,96] 13 (by decide) (choices 2) [3,5,6,9,10,12] r41106 c41106
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41106_3
  · exact m41106_5
  · exact m41106_6
  · exact m41106_9
  · exact m41106_10
  · exact m41106_12

def b41107 : PairBound 9 := { available := 484, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 37 14 500 484 484 484 484), lower := (rows 11 19 37 14 16 32 64 128 256), losses := [] }

theorem u41107 : Upper (D 6) (R 6) [10,17,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41108 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 11 19 37 42 468 484 452 452 452), lower := (rows 11 19 37 42 16 32 64 128 256), losses := [] }

theorem u41108 : Upper (D 6) (R 6) [10,17,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41109 : PairBound 9 := { available := 454, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 37 44 470 486 454 454 454), lower := (rows 11 19 37 44 16 32 64 128 256), losses := [] }

theorem u41109 : Upper (D 6) (R 6) [10,17,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41110 : PairBound 9 := { available := 484, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 37 74 500 484 484 484 484), lower := (rows 11 19 37 74 16 32 64 128 256), losses := [] }

theorem u41110 : Upper (D 6) (R 6) [10,17,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41111 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41111 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41111 : Upper (D 6) (R 6) [10,17,33,68] 13 := by
  apply FastRouting.sound _ _ [10,17,33,68] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,384] r41111 c41111
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29813
  · exact u29814
  · exact u29815
  · exact u29816
  · exact u29817
  · exact u29818
  · exact u29819
  · exact u29820
  · exact u29821
  · exact u29822
  · exact u29823

def r41112 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41112 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41112 : Upper (D 6) (R 6) [10,17,33,96] 13 := by
  apply FastRouting.sound _ _ [10,17,33,96] 13 (by decide) (choices 2) [6,66,68,130,132,192,384] r41112 c41112
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29824
  · exact u29825
  · exact u29826
  · exact u29827
  · exact u29828
  · exact u29829
  · exact u29830

def b41113 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 37 138 372 356 356 484 356), lower := (rows 11 19 37 138 16 32 64 128 256), losses := [] }

theorem u41113 : Upper (D 6) (R 6) [10,17,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41114 : Route 9 := (fun mask => (mask,id))

def c41114 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41114 : Upper (D 6) (R 6) [10,17,33,132] 13 := by
  apply FastRouting.sound _ _ [10,17,33,132] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41114 c41114
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29831
  · exact u29832
  · exact u29833
  · exact u29834
  · exact u29835
  · exact u29836
  · exact u29837
  · exact u29838
  · exact u29839
  · exact u29840

def r41115 : Route 9 := (fun mask => (mask,id))

def c41115 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41115 : Upper (D 6) (R 6) [10,17,33,160] 13 := by
  apply FastRouting.sound _ _ [10,17,33,160] 13 (by decide) (choices 2) [6,66,68,258,260,320] r41115 c41115
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29841
  · exact u29842
  · exact u29843
  · exact u29844
  · exact u29845
  · exact u29846

def r41116 : Route 9 := (fun mask => (mask,id))

def c41116 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41116 : Upper (D 6) (R 6) [10,17,33,192] 13 := by
  apply FastRouting.sound _ _ [10,17,33,192] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41116 c41116
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29847
  · exact u29848
  · exact u29849
  · exact u29850
  · exact u29851
  · exact u29852
  · exact u29853
  · exact u29854
  · exact u29855
  · exact u29856

def r41117 : Route 9 := (fun mask => (mask,id))

def c41117 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41117 : Upper (D 6) (R 6) [10,17,33,384] 13 := by
  apply FastRouting.sound _ _ [10,17,33,384] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41117 c41117
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29857
  · exact u29858
  · exact u29859
  · exact u29860
  · exact u29861
  · exact u29862

def b41118 : PairBound 9 := { available := 484, camps := [{ cop := 4, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 100 11 500 484 484 484 484), lower := (rows 11 19 100 11 16 32 64 128 256), losses := [] }

theorem u41118 : Upper (D 6) (R 6) [10,17,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41119 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41119 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41119 : Upper (D 6) (R 6) [10,17,96,5] 13 := by
  apply FastRouting.sound _ _ [10,17,96,5] 13 (by decide) (choices 2) [6,34,36,96,130,132,160,384] r41119 c41119
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29866
  · exact u29867
  · exact u29868
  · exact u29869
  · exact u29870
  · exact u29871
  · exact u29872
  · exact u29873

def b41120 : PairBound 9 := { available := 485, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 100 14 501 485 485 485 485), lower := (rows 11 19 100 14 16 32 64 128 256), losses := [] }

theorem u41120 : Upper (D 6) (R 6) [10,17,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41121_6 : Upper (D 6) (R 6) [10,17,96,33,6] 13 :=
  permutation_upper _ _ _ [10,17,96,5,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29867

def r41121 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41121 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41121 : Upper (D 6) (R 6) [10,17,96,33] 13 := by
  apply FastRouting.sound _ _ [10,17,96,33] 13 (by decide) (choices 2) [6,66,68,130,132,192,384] r41121 c41121
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41121_6
  · exact u29877
  · exact u29878
  · exact u29879
  · exact u29880
  · exact u29881
  · exact u29882

def b41122 : PairBound 9 := { available := 453, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 100 42 469 485 453 453 453), lower := (rows 11 19 100 42 16 32 64 128 256), losses := [] }

theorem u41122 : Upper (D 6) (R 6) [10,17,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41123 : PairBound 9 := { available := 455, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 100 44 471 487 455 455 455), lower := (rows 11 19 100 44 16 32 64 128 256), losses := [] }

theorem u41123 : Upper (D 6) (R 6) [10,17,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41124 : PairBound 9 := { available := 391, camps := [{ cop := 2, region := 8, targets := 3 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 19 100 104 407 423 455 391 391), lower := (rows 11 19 100 104 16 32 64 128 256), losses := [] }

theorem u41124 : Upper (D 6) (R 6) [10,17,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41125_6 : Upper (D 6) (R 6) [10,17,96,129,6] 13 :=
  permutation_upper _ _ _ [10,17,96,5,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29870

theorem m41125_34 : Upper (D 6) (R 6) [10,17,96,129,34] 13 :=
  permutation_upper _ _ _ [10,17,96,33,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29879

theorem m41125_36 : Upper (D 6) (R 6) [10,17,96,129,36] 13 :=
  permutation_upper _ _ _ [10,17,96,36,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29886

theorem m41125_96 : Upper (D 6) (R 6) [10,17,96,129,96] 13 :=
  permutation_upper _ _ _ [10,17,96,96,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29890

def r41125 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41125 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41125 : Upper (D 6) (R 6) [10,17,96,129] 13 := by
  apply FastRouting.sound _ _ [10,17,96,129] 13 (by decide) (choices 2) [6,34,36,96,258,260,288] r41125 c41125
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41125_6
  · exact m41125_34
  · exact m41125_36
  · exact m41125_96
  · exact u29893
  · exact u29894
  · exact u29895

def b41126 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 100 138 373 357 357 485 357), lower := (rows 11 19 100 138 16 32 64 128 256), losses := [] }

theorem u41126 : Upper (D 6) (R 6) [10,17,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41127_3 : Upper (D 6) (R 6) [10,17,96,132,3] 13 :=
  permutation_upper _ _ _ [10,17,96,3,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29863

theorem m41127_5 : Upper (D 6) (R 6) [10,17,96,132,5] 13 :=
  permutation_upper _ _ _ [10,17,96,6,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29874

theorem m41127_6 : Upper (D 6) (R 6) [10,17,96,132,6] 13 :=
  permutation_upper _ _ _ [10,17,96,5,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29871

theorem m41127_33 : Upper (D 6) (R 6) [10,17,96,132,33] 13 :=
  permutation_upper _ _ _ [10,17,96,34,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29883

theorem m41127_34 : Upper (D 6) (R 6) [10,17,96,132,34] 13 :=
  permutation_upper _ _ _ [10,17,96,33,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29880

theorem m41127_36 : Upper (D 6) (R 6) [10,17,96,132,36] 13 :=
  permutation_upper _ _ _ [10,17,96,36,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29887

theorem m41127_96 : Upper (D 6) (R 6) [10,17,96,132,96] 13 :=
  permutation_upper _ _ _ [10,17,96,96,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29891

theorem m41127_257 : Upper (D 6) (R 6) [10,17,96,132,257] 13 :=
  permutation_upper _ _ _ [10,17,96,130,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29896

theorem m41127_258 : Upper (D 6) (R 6) [10,17,96,132,258] 13 :=
  permutation_upper _ _ _ [10,17,96,129,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29894

def r41127 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41127 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41127 : Upper (D 6) (R 6) [10,17,96,132] 13 := by
  apply FastRouting.sound _ _ [10,17,96,132] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r41127 c41127
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41127_3
  · exact m41127_5
  · exact m41127_6
  · exact m41127_33
  · exact m41127_34
  · exact m41127_36
  · exact m41127_96
  · exact m41127_257
  · exact m41127_258
  · exact u29898
  · exact u29899

theorem m41128_3 : Upper (D 6) (R 6) [10,17,96,160,3] 13 :=
  permutation_upper _ _ _ [10,17,96,3,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29864

theorem m41128_5 : Upper (D 6) (R 6) [10,17,96,160,5] 13 :=
  permutation_upper _ _ _ [10,17,96,6,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29875

theorem m41128_6 : Upper (D 6) (R 6) [10,17,96,160,6] 13 :=
  permutation_upper _ _ _ [10,17,96,5,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29872

theorem m41128_65 : Upper (D 6) (R 6) [10,17,96,160,65] 13 :=
  permutation_upper _ _ _ [10,17,96,34,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29884

theorem m41128_66 : Upper (D 6) (R 6) [10,17,96,160,66] 13 :=
  permutation_upper _ _ _ [10,17,96,33,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29881

theorem m41128_68 : Upper (D 6) (R 6) [10,17,96,160,68] 13 :=
  permutation_upper _ _ _ [10,17,96,36,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29888

theorem m41128_257 : Upper (D 6) (R 6) [10,17,96,160,257] 13 :=
  permutation_upper _ _ _ [10,17,96,130,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29897

theorem m41128_258 : Upper (D 6) (R 6) [10,17,96,160,258] 13 :=
  permutation_upper _ _ _ [10,17,96,129,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29895

theorem m41128_260 : Upper (D 6) (R 6) [10,17,96,160,260] 13 :=
  permutation_upper _ _ _ [10,17,96,132,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29899

def r41128 : Route 9 := (fun mask => (mask,id))

def c41128 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41128 : Upper (D 6) (R 6) [10,17,96,160] 13 := by
  apply FastRouting.sound _ _ [10,17,96,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41128 c41128
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41128_3
  · exact m41128_5
  · exact m41128_6
  · exact m41128_65
  · exact m41128_66
  · exact m41128_68
  · exact m41128_257
  · exact m41128_258
  · exact m41128_260
  · exact u29900

theorem m41129_3 : Upper (D 6) (R 6) [10,17,96,384,3] 13 :=
  permutation_upper _ _ _ [10,17,96,3,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29865

theorem m41129_5 : Upper (D 6) (R 6) [10,17,96,384,5] 13 :=
  permutation_upper _ _ _ [10,17,96,6,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29876

theorem m41129_6 : Upper (D 6) (R 6) [10,17,96,384,6] 13 :=
  permutation_upper _ _ _ [10,17,96,5,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29873

theorem m41129_33 : Upper (D 6) (R 6) [10,17,96,384,33] 13 :=
  permutation_upper _ _ _ [10,17,96,34,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29885

theorem m41129_34 : Upper (D 6) (R 6) [10,17,96,384,34] 13 :=
  permutation_upper _ _ _ [10,17,96,33,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29882

theorem m41129_36 : Upper (D 6) (R 6) [10,17,96,384,36] 13 :=
  permutation_upper _ _ _ [10,17,96,36,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29889

theorem m41129_96 : Upper (D 6) (R 6) [10,17,96,384,96] 13 :=
  permutation_upper _ _ _ [10,17,96,96,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29892

def r41129 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41129 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41129 : Upper (D 6) (R 6) [10,17,96,384] 13 := by
  apply FastRouting.sound _ _ [10,17,96,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41129 c41129
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41129_3
  · exact m41129_5
  · exact m41129_6
  · exact m41129_33
  · exact m41129_34
  · exact m41129_36
  · exact m41129_96

def b41130 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 133 14 372 356 356 484 356), lower := (rows 11 19 133 14 16 32 64 128 256), losses := [] }

theorem u41130 : Upper (D 6) (R 6) [10,17,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41131 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 133 42 372 356 356 484 356), lower := (rows 11 19 133 42 16 32 64 128 256), losses := [] }

theorem u41131 : Upper (D 6) (R 6) [10,17,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41132 : Route 9 := (fun mask => (mask,id))

def c41132 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41132 : Upper (D 6) (R 6) [10,17,129,36] 13 := by
  apply FastRouting.sound _ _ [10,17,129,36] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41132 c41132
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29901
  · exact u29902
  · exact u29903
  · exact u29904
  · exact u29905
  · exact u29906
  · exact u29907
  · exact u29908
  · exact u29909
  · exact u29910

def r41133 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41133 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41133 : Upper (D 6) (R 6) [10,17,129,96] 13 := by
  apply FastRouting.sound _ _ [10,17,129,96] 13 (by decide) (choices 2) [6,34,36,96,258,260,288] r41133 c41133
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29911
  · exact u29912
  · exact u29913
  · exact u29914
  · exact u29915
  · exact u29916
  · exact u29917

def b41134 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 133 266 116 100 100 228 356), lower := (rows 11 19 133 266 16 32 64 128 256), losses := [] }

theorem u41134 : Upper (D 6) (R 6) [10,17,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41135 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41135 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41135 : Upper (D 6) (R 6) [10,17,129,260] 13 := by
  apply FastRouting.sound _ _ [10,17,129,260] 13 (by decide) (choices 2) [6,34,36,96] r41135 c41135
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29918
  · exact u29919
  · exact u29920
  · exact u29921

def r41136 : Route 9 := (fun mask => (mask,id))

def c41136 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41136 : Upper (D 6) (R 6) [10,17,129,288] 13 := by
  apply FastRouting.sound _ _ [10,17,129,288] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41136 c41136
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29922
  · exact u29923
  · exact u29924
  · exact u29925
  · exact u29926
  · exact u29927

def b41137 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 11 372 356 356 484 356), lower := (rows 11 19 164 11 16 32 64 128 256), losses := [] }

theorem u41137 : Upper (D 6) (R 6) [10,17,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41138 : Route 9 := (fun mask => (mask,id))

def c41138 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41138 : Upper (D 6) (R 6) [10,17,160,5] 13 := by
  apply FastRouting.sound _ _ [10,17,160,5] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41138 c41138
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29933
  · exact u29934
  · exact u29935
  · exact u29936
  · exact u29937
  · exact u29938
  · exact u29939
  · exact u29940
  · exact u29941
  · exact u29942

def b41139 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 14 373 357 357 485 357), lower := (rows 11 19 164 14 16 32 64 128 256), losses := [] }

theorem u41139 : Upper (D 6) (R 6) [10,17,160,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41140_6 : Upper (D 6) (R 6) [10,17,160,33,6] 13 :=
  permutation_upper _ _ _ [10,17,160,5,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29934

def r41140 : Route 9 := (fun mask => (mask,id))

def c41140 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41140 : Upper (D 6) (R 6) [10,17,160,33] 13 := by
  apply FastRouting.sound _ _ [10,17,160,33] 13 (by decide) (choices 2) [6,66,68,258,260,320] r41140 c41140
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41140_6
  · exact u29948
  · exact u29949
  · exact u29950
  · exact u29951
  · exact u29952

def b41141 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 42 341 357 325 453 325), lower := (rows 11 19 164 42 16 32 64 128 256), losses := [] }

theorem u41141 : Upper (D 6) (R 6) [10,17,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41142 : PairBound 9 := { available := 327, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 164 44 343 359 327 455 327), lower := (rows 11 19 164 44 16 32 64 128 256), losses := [] }

theorem u41142 : Upper (D 6) (R 6) [10,17,160,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41143_6 : Upper (D 6) (R 6) [10,17,160,65,6] 13 :=
  permutation_upper _ _ _ [10,17,160,5,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29936

theorem m41143_34 : Upper (D 6) (R 6) [10,17,160,65,34] 13 :=
  permutation_upper _ _ _ [10,17,160,33,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29948

theorem m41143_36 : Upper (D 6) (R 6) [10,17,160,65,36] 13 :=
  permutation_upper _ _ _ [10,17,160,36,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29956

def r41143 : Route 9 := (fun mask => (mask,id))

def c41143 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41143 : Upper (D 6) (R 6) [10,17,160,65] 13 := by
  apply FastRouting.sound _ _ [10,17,160,65] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41143 c41143
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41143_6
  · exact m41143_34
  · exact m41143_36
  · exact u29961
  · exact u29962
  · exact u29963
  · exact u29964
  · exact u29965
  · exact u29966
  · exact u29967

def b41144 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 74 373 357 357 485 357), lower := (rows 11 19 164 74 16 32 64 128 256), losses := [] }

theorem u41144 : Upper (D 6) (R 6) [10,17,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41145_3 : Upper (D 6) (R 6) [10,17,160,68,3] 13 :=
  permutation_upper _ _ _ [10,17,160,3,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29928

theorem m41145_5 : Upper (D 6) (R 6) [10,17,160,68,5] 13 :=
  permutation_upper _ _ _ [10,17,160,6,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29943

theorem m41145_6 : Upper (D 6) (R 6) [10,17,160,68,6] 13 :=
  permutation_upper _ _ _ [10,17,160,5,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29937

theorem m41145_33 : Upper (D 6) (R 6) [10,17,160,68,33] 13 :=
  permutation_upper _ _ _ [10,17,160,34,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29953

theorem m41145_34 : Upper (D 6) (R 6) [10,17,160,68,34] 13 :=
  permutation_upper _ _ _ [10,17,160,33,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29949

theorem m41145_36 : Upper (D 6) (R 6) [10,17,160,68,36] 13 :=
  permutation_upper _ _ _ [10,17,160,36,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29957

theorem m41145_65 : Upper (D 6) (R 6) [10,17,160,68,65] 13 :=
  permutation_upper _ _ _ [10,17,160,66,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29968

theorem m41145_66 : Upper (D 6) (R 6) [10,17,160,68,66] 13 :=
  permutation_upper _ _ _ [10,17,160,65,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29962

def r41145 : Route 9 := (fun mask => (mask,id))

def c41145 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41145 : Upper (D 6) (R 6) [10,17,160,68] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41145 c41145
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41145_3
  · exact m41145_5
  · exact m41145_6
  · exact m41145_33
  · exact m41145_34
  · exact m41145_36
  · exact m41145_65
  · exact m41145_66
  · exact u29973
  · exact u29974
  · exact u29975
  · exact u29976
  · exact u29977
  · exact u29978
  · exact u29979

theorem m41146_3 : Upper (D 6) (R 6) [10,17,160,96,3] 13 :=
  permutation_upper _ _ _ [10,17,160,3,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29929

theorem m41146_5 : Upper (D 6) (R 6) [10,17,160,96,5] 13 :=
  permutation_upper _ _ _ [10,17,160,6,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29944

theorem m41146_6 : Upper (D 6) (R 6) [10,17,160,96,6] 13 :=
  permutation_upper _ _ _ [10,17,160,5,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29938

theorem m41146_65 : Upper (D 6) (R 6) [10,17,160,96,65] 13 :=
  permutation_upper _ _ _ [10,17,160,66,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29969

theorem m41146_66 : Upper (D 6) (R 6) [10,17,160,96,66] 13 :=
  permutation_upper _ _ _ [10,17,160,65,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29963

theorem m41146_68 : Upper (D 6) (R 6) [10,17,160,96,68] 13 :=
  permutation_upper _ _ _ [10,17,160,68,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29974

def r41146 : Route 9 := (fun mask => (mask,id))

def c41146 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41146 : Upper (D 6) (R 6) [10,17,160,96] 13 := by
  apply FastRouting.sound _ _ [10,17,160,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41146 c41146
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41146_3
  · exact m41146_5
  · exact m41146_6
  · exact m41146_65
  · exact m41146_66
  · exact m41146_68
  · exact u29980
  · exact u29981
  · exact u29982
  · exact u29983

theorem m41147_6 : Upper (D 6) (R 6) [10,17,160,257,6] 13 :=
  permutation_upper _ _ _ [10,17,160,5,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29939

theorem m41147_34 : Upper (D 6) (R 6) [10,17,160,257,34] 13 :=
  permutation_upper _ _ _ [10,17,160,33,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29950

theorem m41147_36 : Upper (D 6) (R 6) [10,17,160,257,36] 13 :=
  permutation_upper _ _ _ [10,17,160,36,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29958

theorem m41147_66 : Upper (D 6) (R 6) [10,17,160,257,66] 13 :=
  permutation_upper _ _ _ [10,17,160,65,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29964

theorem m41147_68 : Upper (D 6) (R 6) [10,17,160,257,68] 13 :=
  permutation_upper _ _ _ [10,17,160,68,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29976

theorem m41147_96 : Upper (D 6) (R 6) [10,17,160,257,96] 13 :=
  permutation_upper _ _ _ [10,17,160,96,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29981

def r41147 : Route 9 := (fun mask => (mask,id))

def c41147 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41147 : Upper (D 6) (R 6) [10,17,160,257] 13 := by
  apply FastRouting.sound _ _ [10,17,160,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41147 c41147
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41147_6
  · exact m41147_34
  · exact m41147_36
  · exact m41147_66
  · exact m41147_68
  · exact m41147_96

def b41148 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 266 117 101 101 229 357), lower := (rows 11 19 164 266 16 32 64 128 256), losses := [] }

theorem u41148 : Upper (D 6) (R 6) [10,17,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41149_3 : Upper (D 6) (R 6) [10,17,160,260,3] 13 :=
  permutation_upper _ _ _ [10,17,160,3,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29930

theorem m41149_5 : Upper (D 6) (R 6) [10,17,160,260,5] 13 :=
  permutation_upper _ _ _ [10,17,160,6,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29945

theorem m41149_6 : Upper (D 6) (R 6) [10,17,160,260,6] 13 :=
  permutation_upper _ _ _ [10,17,160,5,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29940

theorem m41149_33 : Upper (D 6) (R 6) [10,17,160,260,33] 13 :=
  permutation_upper _ _ _ [10,17,160,34,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29954

theorem m41149_34 : Upper (D 6) (R 6) [10,17,160,260,34] 13 :=
  permutation_upper _ _ _ [10,17,160,33,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29951

theorem m41149_36 : Upper (D 6) (R 6) [10,17,160,260,36] 13 :=
  permutation_upper _ _ _ [10,17,160,36,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29959

theorem m41149_65 : Upper (D 6) (R 6) [10,17,160,260,65] 13 :=
  permutation_upper _ _ _ [10,17,160,66,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29970

theorem m41149_66 : Upper (D 6) (R 6) [10,17,160,260,66] 13 :=
  permutation_upper _ _ _ [10,17,160,65,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29965

theorem m41149_68 : Upper (D 6) (R 6) [10,17,160,260,68] 13 :=
  permutation_upper _ _ _ [10,17,160,68,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29977

theorem m41149_96 : Upper (D 6) (R 6) [10,17,160,260,96] 13 :=
  permutation_upper _ _ _ [10,17,160,96,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29982

def r41149 : Route 9 := (fun mask => (mask,id))

def c41149 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41149 : Upper (D 6) (R 6) [10,17,160,260] 13 := by
  apply FastRouting.sound _ _ [10,17,160,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41149 c41149
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41149_3
  · exact m41149_5
  · exact m41149_6
  · exact m41149_33
  · exact m41149_34
  · exact m41149_36
  · exact m41149_65
  · exact m41149_66
  · exact m41149_68
  · exact m41149_96

theorem m41150_3 : Upper (D 6) (R 6) [10,17,160,288,3] 13 :=
  permutation_upper _ _ _ [10,17,160,3,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29931

theorem m41150_5 : Upper (D 6) (R 6) [10,17,160,288,5] 13 :=
  permutation_upper _ _ _ [10,17,160,6,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29946

theorem m41150_6 : Upper (D 6) (R 6) [10,17,160,288,6] 13 :=
  permutation_upper _ _ _ [10,17,160,5,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29941

theorem m41150_65 : Upper (D 6) (R 6) [10,17,160,288,65] 13 :=
  permutation_upper _ _ _ [10,17,160,66,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29971

theorem m41150_66 : Upper (D 6) (R 6) [10,17,160,288,66] 13 :=
  permutation_upper _ _ _ [10,17,160,65,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29966

theorem m41150_68 : Upper (D 6) (R 6) [10,17,160,288,68] 13 :=
  permutation_upper _ _ _ [10,17,160,68,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29978

def r41150 : Route 9 := (fun mask => (mask,id))

def c41150 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41150 : Upper (D 6) (R 6) [10,17,160,288] 13 := by
  apply FastRouting.sound _ _ [10,17,160,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41150 c41150
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41150_3
  · exact m41150_5
  · exact m41150_6
  · exact m41150_65
  · exact m41150_66
  · exact m41150_68

theorem m41151_3 : Upper (D 6) (R 6) [10,17,160,320,3] 13 :=
  permutation_upper _ _ _ [10,17,160,3,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29932

theorem m41151_5 : Upper (D 6) (R 6) [10,17,160,320,5] 13 :=
  permutation_upper _ _ _ [10,17,160,6,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29947

theorem m41151_6 : Upper (D 6) (R 6) [10,17,160,320,6] 13 :=
  permutation_upper _ _ _ [10,17,160,5,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29942

theorem m41151_33 : Upper (D 6) (R 6) [10,17,160,320,33] 13 :=
  permutation_upper _ _ _ [10,17,160,34,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29955

theorem m41151_34 : Upper (D 6) (R 6) [10,17,160,320,34] 13 :=
  permutation_upper _ _ _ [10,17,160,33,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29952

theorem m41151_36 : Upper (D 6) (R 6) [10,17,160,320,36] 13 :=
  permutation_upper _ _ _ [10,17,160,36,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29960

theorem m41151_65 : Upper (D 6) (R 6) [10,17,160,320,65] 13 :=
  permutation_upper _ _ _ [10,17,160,66,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29972

theorem m41151_66 : Upper (D 6) (R 6) [10,17,160,320,66] 13 :=
  permutation_upper _ _ _ [10,17,160,65,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29967

theorem m41151_68 : Upper (D 6) (R 6) [10,17,160,320,68] 13 :=
  permutation_upper _ _ _ [10,17,160,68,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29979

theorem m41151_96 : Upper (D 6) (R 6) [10,17,160,320,96] 13 :=
  permutation_upper _ _ _ [10,17,160,96,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29983

def r41151 : Route 9 := (fun mask => (mask,id))

def c41151 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41151 : Upper (D 6) (R 6) [10,17,160,320] 13 := by
  apply FastRouting.sound _ _ [10,17,160,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41151 c41151
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41151_3
  · exact m41151_5
  · exact m41151_6
  · exact m41151_33
  · exact m41151_34
  · exact m41151_36
  · exact m41151_65
  · exact m41151_66
  · exact m41151_68
  · exact m41151_96

def b41152 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 388 11 116 100 100 228 356), lower := (rows 11 19 388 11 16 32 64 128 256), losses := [] }

theorem u41152 : Upper (D 6) (R 6) [10,17,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41153 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41153 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41153 : Upper (D 6) (R 6) [10,17,384,5] 13 := by
  apply FastRouting.sound _ _ [10,17,384,5] 13 (by decide) (choices 2) [6,34,36,96] r41153 c41153
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29986
  · exact u29987
  · exact u29988
  · exact u29989

def b41154 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 388 14 117 101 101 229 357), lower := (rows 11 19 388 14 16 32 64 128 256), losses := [] }

theorem u41154 : Upper (D 6) (R 6) [10,17,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41155_6 : Upper (D 6) (R 6) [10,17,384,33,6] 13 :=
  permutation_upper _ _ _ [10,17,384,5,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29987

def r41155 : Route 9 := (fun mask => (mask,id))

def c41155 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41155 : Upper (D 6) (R 6) [10,17,384,33] 13 := by
  apply FastRouting.sound _ _ [10,17,384,33] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41155 c41155
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41155_6
  · exact u29992
  · exact u29993
  · exact u29994
  · exact u29995
  · exact u29996

def b41156 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 388 42 117 101 101 229 357), lower := (rows 11 19 388 42 16 32 64 128 256), losses := [] }

theorem u41156 : Upper (D 6) (R 6) [10,17,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41157_3 : Upper (D 6) (R 6) [10,17,384,36,3] 13 :=
  permutation_upper _ _ _ [10,17,384,3,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29984

theorem m41157_5 : Upper (D 6) (R 6) [10,17,384,36,5] 13 :=
  permutation_upper _ _ _ [10,17,384,6,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29990

theorem m41157_6 : Upper (D 6) (R 6) [10,17,384,36,6] 13 :=
  permutation_upper _ _ _ [10,17,384,5,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29988

theorem m41157_33 : Upper (D 6) (R 6) [10,17,384,36,33] 13 :=
  permutation_upper _ _ _ [10,17,384,34,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29997

theorem m41157_34 : Upper (D 6) (R 6) [10,17,384,36,34] 13 :=
  permutation_upper _ _ _ [10,17,384,33,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29993

theorem m41157_65 : Upper (D 6) (R 6) [10,17,384,36,65] 13 :=
  permutation_upper _ _ _ [10,17,384,34,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29998

theorem m41157_66 : Upper (D 6) (R 6) [10,17,384,36,66] 13 :=
  permutation_upper _ _ _ [10,17,384,33,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29995

def r41157 : Route 9 := (fun mask => (mask,id))

def c41157 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41157 : Upper (D 6) (R 6) [10,17,384,36] 13 := by
  apply FastRouting.sound _ _ [10,17,384,36] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41157 c41157
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41157_3
  · exact m41157_5
  · exact m41157_6
  · exact m41157_33
  · exact m41157_34
  · exact u30000
  · exact m41157_65
  · exact m41157_66
  · exact u30001
  · exact u30002

theorem m41158_3 : Upper (D 6) (R 6) [10,17,384,96,3] 13 :=
  permutation_upper _ _ _ [10,17,384,3,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29985

theorem m41158_5 : Upper (D 6) (R 6) [10,17,384,96,5] 13 :=
  permutation_upper _ _ _ [10,17,384,6,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29991

theorem m41158_6 : Upper (D 6) (R 6) [10,17,384,96,6] 13 :=
  permutation_upper _ _ _ [10,17,384,5,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29989

theorem m41158_33 : Upper (D 6) (R 6) [10,17,384,96,33] 13 :=
  permutation_upper _ _ _ [10,17,384,34,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29999

theorem m41158_34 : Upper (D 6) (R 6) [10,17,384,96,34] 13 :=
  permutation_upper _ _ _ [10,17,384,33,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29996

theorem m41158_36 : Upper (D 6) (R 6) [10,17,384,96,36] 13 :=
  permutation_upper _ _ _ [10,17,384,36,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30002

def r41158 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41158 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41158 : Upper (D 6) (R 6) [10,17,384,96] 13 := by
  apply FastRouting.sound _ _ [10,17,384,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41158 c41158
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41158_3
  · exact m41158_5
  · exact m41158_6
  · exact m41158_33
  · exact m41158_34
  · exact m41158_36
  · exact u30003

def b41159 : PairBound 9 := { available := 484, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 37 11 500 484 484 484 484), lower := (rows 11 22 37 11 16 32 64 128 256), losses := [] }

theorem u41159 : Upper (D 6) (R 6) [10,20,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u41159
end Delivery.IrregularNine14.P06
