import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0628
import IrregularNine14P06C0629
import IrregularNine14P06C0630
import IrregularNine14P06C0631
import IrregularNine14P06C0632

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b42960 : PairBound 9 := { available := 55, camps := [{ cop := 2, region := 179, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 76 328 55 55 119 183 311), lower := (rows 35 134 76 328 16 32 64 128 256), losses := [] }

theorem u42960 : Upper (D 6) (R 6) [34,132,72,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42961 : PairBound 9 := { available := 349, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 100 11 349 381 349 477 349), lower := (rows 35 134 100 11 16 32 64 128 256), losses := [] }

theorem u42961 : Upper (D 6) (R 6) [34,132,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42962_3 : Upper (D 6) (R 6) [34,132,96,5,3] 13 :=
  permutation_upper _ _ _ [34,132,96,3,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37682

def r42962 : Route 9 := (fun mask => (mask,id))

def c42962 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42962 : Upper (D 6) (R 6) [34,132,96,5] 13 := by
  apply FastRouting.sound _ _ [34,132,96,5] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r42962 c42962
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42962_3
  · exact u37691
  · exact u37692
  · exact u37693
  · exact u37694
  · exact u37695
  · exact u37696
  · exact u37697
  · exact u37698
  · exact u37699

def b42963 : PairBound 9 := { available := 345, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 100 14 345 377 345 473 345), lower := (rows 35 134 100 14 16 32 64 128 256), losses := [] }

theorem u42963 : Upper (D 6) (R 6) [34,132,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42964_3 : Upper (D 6) (R 6) [34,132,96,17,3] 13 :=
  permutation_upper _ _ _ [34,132,96,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37683

theorem m42964_5 : Upper (D 6) (R 6) [34,132,96,17,5] 13 :=
  permutation_upper _ _ _ [34,132,96,5,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37691

theorem m42964_6 : Upper (D 6) (R 6) [34,132,96,17,6] 13 :=
  permutation_upper _ _ _ [34,132,96,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37700

def r42964 : Route 9 := (fun mask => (mask,id))

def c42964 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42964 : Upper (D 6) (R 6) [34,132,96,17] 13 := by
  apply FastRouting.sound _ _ [34,132,96,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72,257,258,260,264,320] r42964 c42964
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42964_3
  · exact m42964_5
  · exact m42964_6
  · exact u37706
  · exact u37707
  · exact u37708
  · exact u37709
  · exact u37710
  · exact u37711
  · exact u37712
  · exact u37713
  · exact u37714
  · exact u37715
  · exact u37716
  · exact u37717

theorem m42965_5 : Upper (D 6) (R 6) [34,132,96,18,5] 13 :=
  permutation_upper _ _ _ [34,132,96,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37692

theorem m42965_9 : Upper (D 6) (R 6) [34,132,96,18,9] 13 :=
  permutation_upper _ _ _ [34,132,96,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37707

def r42965 : Route 9 := (fun mask => (mask,id))

def c42965 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42965 : Upper (D 6) (R 6) [34,132,96,18] 13 := by
  apply FastRouting.sound _ _ [34,132,96,18] 13 (by decide) (choices 2) [5,9,12,65,68,72,257,260,264,320] r42965 c42965
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42965_5
  · exact m42965_9
  · exact u37718
  · exact u37719
  · exact u37720
  · exact u37721
  · exact u37722
  · exact u37723
  · exact u37724
  · exact u37725

theorem m42966_3 : Upper (D 6) (R 6) [34,132,96,20,3] 13 :=
  permutation_upper _ _ _ [34,132,96,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37684

theorem m42966_9 : Upper (D 6) (R 6) [34,132,96,20,9] 13 :=
  permutation_upper _ _ _ [34,132,96,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37708

theorem m42966_10 : Upper (D 6) (R 6) [34,132,96,20,10] 13 :=
  permutation_upper _ _ _ [34,132,96,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37718

def r42966 : Route 9 := (fun mask => (mask,id))

def c42966 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42966 : Upper (D 6) (R 6) [34,132,96,20] 13 := by
  apply FastRouting.sound _ _ [34,132,96,20] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r42966 c42966
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42966_3
  · exact m42966_9
  · exact m42966_10
  · exact u37726
  · exact u37727
  · exact u37728
  · exact u37729
  · exact u37730
  · exact u37731
  · exact u37732

theorem m42967_3 : Upper (D 6) (R 6) [34,132,96,65,3] 13 :=
  permutation_upper _ _ _ [34,132,96,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37685

theorem m42967_5 : Upper (D 6) (R 6) [34,132,96,65,5] 13 :=
  permutation_upper _ _ _ [34,132,96,5,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37693

theorem m42967_6 : Upper (D 6) (R 6) [34,132,96,65,6] 13 :=
  permutation_upper _ _ _ [34,132,96,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37701

theorem m42967_9 : Upper (D 6) (R 6) [34,132,96,65,9] 13 :=
  permutation_upper _ _ _ [34,132,96,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37709

theorem m42967_10 : Upper (D 6) (R 6) [34,132,96,65,10] 13 :=
  permutation_upper _ _ _ [34,132,96,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37719

theorem m42967_12 : Upper (D 6) (R 6) [34,132,96,65,12] 13 :=
  permutation_upper _ _ _ [34,132,96,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37726

def r42967 : Route 9 := (fun mask => (mask,id))

def c42967 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42967 : Upper (D 6) (R 6) [34,132,96,65] 13 := by
  apply FastRouting.sound _ _ [34,132,96,65] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r42967 c42967
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42967_3
  · exact m42967_5
  · exact m42967_6
  · exact m42967_9
  · exact m42967_10
  · exact m42967_12
  · exact u37733
  · exact u37734
  · exact u37735
  · exact u37736

theorem m42968_5 : Upper (D 6) (R 6) [34,132,96,66,5] 13 :=
  permutation_upper _ _ _ [34,132,96,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37694

theorem m42968_9 : Upper (D 6) (R 6) [34,132,96,66,9] 13 :=
  permutation_upper _ _ _ [34,132,96,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37710

theorem m42968_12 : Upper (D 6) (R 6) [34,132,96,66,12] 13 :=
  permutation_upper _ _ _ [34,132,96,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37727

def r42968 : Route 9 := (fun mask => (mask,id))

def c42968 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42968 : Upper (D 6) (R 6) [34,132,96,66] 13 := by
  apply FastRouting.sound _ _ [34,132,96,66] 13 (by decide) (choices 2) [5,9,12,257,260,264] r42968 c42968
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42968_5
  · exact m42968_9
  · exact m42968_12
  · exact u37737
  · exact u37738
  · exact u37739

def b42969 : PairBound 9 := { available := 283, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 134 100 76 283 315 347 411 283), lower := (rows 35 134 100 76 16 32 64 128 256), losses := [] }

theorem u42969 : Upper (D 6) (R 6) [34,132,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42970_3 : Upper (D 6) (R 6) [34,132,96,80,3] 13 :=
  permutation_upper _ _ _ [34,132,96,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37686

theorem m42970_5 : Upper (D 6) (R 6) [34,132,96,80,5] 13 :=
  permutation_upper _ _ _ [34,132,96,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37695

theorem m42970_6 : Upper (D 6) (R 6) [34,132,96,80,6] 13 :=
  permutation_upper _ _ _ [34,132,96,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37702

theorem m42970_9 : Upper (D 6) (R 6) [34,132,96,80,9] 13 :=
  permutation_upper _ _ _ [34,132,96,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37712

theorem m42970_10 : Upper (D 6) (R 6) [34,132,96,80,10] 13 :=
  permutation_upper _ _ _ [34,132,96,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37721

theorem m42970_12 : Upper (D 6) (R 6) [34,132,96,80,12] 13 :=
  permutation_upper _ _ _ [34,132,96,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37728

def r42970 : Route 9 := (fun mask => (mask,id))

def c42970 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42970 : Upper (D 6) (R 6) [34,132,96,80] 13 := by
  apply FastRouting.sound _ _ [34,132,96,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r42970 c42970
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42970_3
  · exact m42970_5
  · exact m42970_6
  · exact m42970_9
  · exact m42970_10
  · exact m42970_12
  · exact u37743
  · exact u37744
  · exact u37745
  · exact u37746

theorem m42971_3 : Upper (D 6) (R 6) [34,132,96,257,3] 13 :=
  permutation_upper _ _ _ [34,132,96,3,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37687

theorem m42971_5 : Upper (D 6) (R 6) [34,132,96,257,5] 13 :=
  permutation_upper _ _ _ [34,132,96,5,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37696

theorem m42971_6 : Upper (D 6) (R 6) [34,132,96,257,6] 13 :=
  permutation_upper _ _ _ [34,132,96,6,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37703

theorem m42971_9 : Upper (D 6) (R 6) [34,132,96,257,9] 13 :=
  permutation_upper _ _ _ [34,132,96,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37713

theorem m42971_10 : Upper (D 6) (R 6) [34,132,96,257,10] 13 :=
  permutation_upper _ _ _ [34,132,96,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37722

theorem m42971_12 : Upper (D 6) (R 6) [34,132,96,257,12] 13 :=
  permutation_upper _ _ _ [34,132,96,20,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37729

theorem m42971_65 : Upper (D 6) (R 6) [34,132,96,257,65] 13 :=
  permutation_upper _ _ _ [34,132,96,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37733

theorem m42971_66 : Upper (D 6) (R 6) [34,132,96,257,66] 13 :=
  permutation_upper _ _ _ [34,132,96,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37737

theorem m42971_68 : Upper (D 6) (R 6) [34,132,96,257,68] 13 :=
  permutation_upper _ _ _ [34,132,96,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37740

theorem m42971_72 : Upper (D 6) (R 6) [34,132,96,257,72] 13 :=
  permutation_upper _ _ _ [34,132,96,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37743

def r42971 : Route 9 := (fun mask => (mask,id))

def c42971 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42971 : Upper (D 6) (R 6) [34,132,96,257] 13 := by
  apply FastRouting.sound _ _ [34,132,96,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42971 c42971
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42971_3
  · exact m42971_5
  · exact m42971_6
  · exact m42971_9
  · exact m42971_10
  · exact m42971_12
  · exact m42971_65
  · exact m42971_66
  · exact m42971_68
  · exact m42971_72

theorem m42972_5 : Upper (D 6) (R 6) [34,132,96,258,5] 13 :=
  permutation_upper _ _ _ [34,132,96,5,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37697

theorem m42972_9 : Upper (D 6) (R 6) [34,132,96,258,9] 13 :=
  permutation_upper _ _ _ [34,132,96,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37714

theorem m42972_12 : Upper (D 6) (R 6) [34,132,96,258,12] 13 :=
  permutation_upper _ _ _ [34,132,96,20,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37730

theorem m42972_65 : Upper (D 6) (R 6) [34,132,96,258,65] 13 :=
  permutation_upper _ _ _ [34,132,96,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37734

theorem m42972_68 : Upper (D 6) (R 6) [34,132,96,258,68] 13 :=
  permutation_upper _ _ _ [34,132,96,68,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37741

theorem m42972_72 : Upper (D 6) (R 6) [34,132,96,258,72] 13 :=
  permutation_upper _ _ _ [34,132,96,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37744

def r42972 : Route 9 := (fun mask => (mask,id))

def c42972 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42972 : Upper (D 6) (R 6) [34,132,96,258] 13 := by
  apply FastRouting.sound _ _ [34,132,96,258] 13 (by decide) (choices 2) [5,9,12,65,68,72] r42972 c42972
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42972_5
  · exact m42972_9
  · exact m42972_12
  · exact m42972_65
  · exact m42972_68
  · exact m42972_72

theorem m42973_3 : Upper (D 6) (R 6) [34,132,96,260,3] 13 :=
  permutation_upper _ _ _ [34,132,96,3,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37688

theorem m42973_9 : Upper (D 6) (R 6) [34,132,96,260,9] 13 :=
  permutation_upper _ _ _ [34,132,96,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37715

theorem m42973_10 : Upper (D 6) (R 6) [34,132,96,260,10] 13 :=
  permutation_upper _ _ _ [34,132,96,18,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37723

theorem m42973_65 : Upper (D 6) (R 6) [34,132,96,260,65] 13 :=
  permutation_upper _ _ _ [34,132,96,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37735

theorem m42973_66 : Upper (D 6) (R 6) [34,132,96,260,66] 13 :=
  permutation_upper _ _ _ [34,132,96,66,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37738

theorem m42973_72 : Upper (D 6) (R 6) [34,132,96,260,72] 13 :=
  permutation_upper _ _ _ [34,132,96,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37745

def r42973 : Route 9 := (fun mask => (mask,id))

def c42973 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42973 : Upper (D 6) (R 6) [34,132,96,260] 13 := by
  apply FastRouting.sound _ _ [34,132,96,260] 13 (by decide) (choices 2) [3,9,10,65,66,72] r42973 c42973
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42973_3
  · exact m42973_9
  · exact m42973_10
  · exact m42973_65
  · exact m42973_66
  · exact m42973_72

theorem m42974_3 : Upper (D 6) (R 6) [34,132,96,272,3] 13 :=
  permutation_upper _ _ _ [34,132,96,3,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37689

theorem m42974_5 : Upper (D 6) (R 6) [34,132,96,272,5] 13 :=
  permutation_upper _ _ _ [34,132,96,5,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37698

theorem m42974_6 : Upper (D 6) (R 6) [34,132,96,272,6] 13 :=
  permutation_upper _ _ _ [34,132,96,6,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37704

theorem m42974_9 : Upper (D 6) (R 6) [34,132,96,272,9] 13 :=
  permutation_upper _ _ _ [34,132,96,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37716

theorem m42974_10 : Upper (D 6) (R 6) [34,132,96,272,10] 13 :=
  permutation_upper _ _ _ [34,132,96,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37724

theorem m42974_12 : Upper (D 6) (R 6) [34,132,96,272,12] 13 :=
  permutation_upper _ _ _ [34,132,96,20,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37731

theorem m42974_65 : Upper (D 6) (R 6) [34,132,96,272,65] 13 :=
  permutation_upper _ _ _ [34,132,96,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37736

theorem m42974_66 : Upper (D 6) (R 6) [34,132,96,272,66] 13 :=
  permutation_upper _ _ _ [34,132,96,66,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37739

theorem m42974_68 : Upper (D 6) (R 6) [34,132,96,272,68] 13 :=
  permutation_upper _ _ _ [34,132,96,68,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37742

theorem m42974_72 : Upper (D 6) (R 6) [34,132,96,272,72] 13 :=
  permutation_upper _ _ _ [34,132,96,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37746

def r42974 : Route 9 := (fun mask => (mask,id))

def c42974 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42974 : Upper (D 6) (R 6) [34,132,96,272] 13 := by
  apply FastRouting.sound _ _ [34,132,96,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42974 c42974
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42974_3
  · exact m42974_5
  · exact m42974_6
  · exact m42974_9
  · exact m42974_10
  · exact m42974_12
  · exact m42974_65
  · exact m42974_66
  · exact m42974_68
  · exact m42974_72

theorem m42975_3 : Upper (D 6) (R 6) [34,132,96,320,3] 13 :=
  permutation_upper _ _ _ [34,132,96,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37690

theorem m42975_5 : Upper (D 6) (R 6) [34,132,96,320,5] 13 :=
  permutation_upper _ _ _ [34,132,96,5,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37699

theorem m42975_6 : Upper (D 6) (R 6) [34,132,96,320,6] 13 :=
  permutation_upper _ _ _ [34,132,96,6,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37705

theorem m42975_9 : Upper (D 6) (R 6) [34,132,96,320,9] 13 :=
  permutation_upper _ _ _ [34,132,96,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37717

theorem m42975_10 : Upper (D 6) (R 6) [34,132,96,320,10] 13 :=
  permutation_upper _ _ _ [34,132,96,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37725

theorem m42975_12 : Upper (D 6) (R 6) [34,132,96,320,12] 13 :=
  permutation_upper _ _ _ [34,132,96,20,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37732

def r42975 : Route 9 := (fun mask => (mask,id))

def c42975 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42975 : Upper (D 6) (R 6) [34,132,96,320] 13 := by
  apply FastRouting.sound _ _ [34,132,96,320] 13 (by decide) (choices 2) [3,5,6,9,10,12] r42975 c42975
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42975_3
  · exact m42975_5
  · exact m42975_6
  · exact m42975_9
  · exact m42975_10
  · exact m42975_12

def b42976 : PairBound 9 := { available := 124, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 261 11 124 124 124 252 380), lower := (rows 35 134 261 11 16 32 64 128 256), losses := [] }

theorem u42976 : Upper (D 6) (R 6) [34,132,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42977 : PairBound 9 := { available := 122, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 134 261 13 122 122 122 250 378), lower := (rows 35 134 261 13 16 32 64 128 256), losses := [] }

theorem u42977 : Upper (D 6) (R 6) [34,132,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42978 : PairBound 9 := { available := 121, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 261 14 121 121 121 249 377), lower := (rows 35 134 261 14 16 32 64 128 256), losses := [] }

theorem u42978 : Upper (D 6) (R 6) [34,132,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42979_6 : Upper (D 6) (R 6) [34,132,257,17,6] 13 :=
  permutation_upper _ _ _ [34,132,257,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37758

def r42979 : Route 9 := (fun mask => (mask,id))

def c42979 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42979 : Upper (D 6) (R 6) [34,132,257,17] 13 := by
  apply FastRouting.sound _ _ [34,132,257,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r42979 c42979
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42979_6
  · exact u37763
  · exact u37764
  · exact u37765
  · exact u37766
  · exact u37767
  · exact u37768
  · exact u37769
  · exact u37770
  · exact u37771

theorem m42980_5 : Upper (D 6) (R 6) [34,132,257,18,5] 13 :=
  permutation_upper _ _ _ [34,132,257,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37753

theorem m42980_9 : Upper (D 6) (R 6) [34,132,257,18,9] 13 :=
  permutation_upper _ _ _ [34,132,257,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37763

def r42980 : Route 9 := (fun mask => (mask,id))

def c42980 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42980 : Upper (D 6) (R 6) [34,132,257,18] 13 := by
  apply FastRouting.sound _ _ [34,132,257,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r42980 c42980
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42980_5
  · exact m42980_9
  · exact u37772
  · exact u37773
  · exact u37774
  · exact u37775
  · exact u37776
  · exact u37777
  · exact u37778
  · exact u37779

theorem m42981_3 : Upper (D 6) (R 6) [34,132,257,20,3] 13 :=
  permutation_upper _ _ _ [34,132,257,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37747

theorem m42981_9 : Upper (D 6) (R 6) [34,132,257,20,9] 13 :=
  permutation_upper _ _ _ [34,132,257,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37764

theorem m42981_10 : Upper (D 6) (R 6) [34,132,257,20,10] 13 :=
  permutation_upper _ _ _ [34,132,257,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37772

def r42981 : Route 9 := (fun mask => (mask,id))

def c42981 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42981 : Upper (D 6) (R 6) [34,132,257,20] 13 := by
  apply FastRouting.sound _ _ [34,132,257,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r42981 c42981
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42981_3
  · exact m42981_9
  · exact m42981_10
  · exact u37780
  · exact u37781
  · exact u37782
  · exact u37783
  · exact u37784
  · exact u37785
  · exact u37786

def b42982 : PairBound 9 := { available := 94, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 261 41 94 126 94 222 350), lower := (rows 35 134 261 41 16 32 64 128 256), losses := [] }

theorem u42982 : Upper (D 6) (R 6) [34,132,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42983 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 134 261 42 93 125 93 221 349), lower := (rows 35 134 261 42 16 32 64 128 256), losses := [] }

theorem u42983 : Upper (D 6) (R 6) [34,132,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42984_3 : Upper (D 6) (R 6) [34,132,257,36,3] 13 :=
  permutation_upper _ _ _ [34,132,257,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37748

theorem m42984_9 : Upper (D 6) (R 6) [34,132,257,36,9] 13 :=
  permutation_upper _ _ _ [34,132,257,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37766

theorem m42984_10 : Upper (D 6) (R 6) [34,132,257,36,10] 13 :=
  permutation_upper _ _ _ [34,132,257,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37774

def r42984 : Route 9 := (fun mask => (mask,id))

def c42984 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42984 : Upper (D 6) (R 6) [34,132,257,36] 13 := by
  apply FastRouting.sound _ _ [34,132,257,36] 13 (by decide) (choices 2) [3,9,10,65,66,72] r42984 c42984
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42984_3
  · exact m42984_9
  · exact m42984_10
  · exact u37793
  · exact u37794
  · exact u37795

theorem m42985_3 : Upper (D 6) (R 6) [34,132,257,48,3] 13 :=
  permutation_upper _ _ _ [34,132,257,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37749

theorem m42985_5 : Upper (D 6) (R 6) [34,132,257,48,5] 13 :=
  permutation_upper _ _ _ [34,132,257,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37754

theorem m42985_6 : Upper (D 6) (R 6) [34,132,257,48,6] 13 :=
  permutation_upper _ _ _ [34,132,257,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37759

theorem m42985_9 : Upper (D 6) (R 6) [34,132,257,48,9] 13 :=
  permutation_upper _ _ _ [34,132,257,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37767

theorem m42985_10 : Upper (D 6) (R 6) [34,132,257,48,10] 13 :=
  permutation_upper _ _ _ [34,132,257,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37775

theorem m42985_12 : Upper (D 6) (R 6) [34,132,257,48,12] 13 :=
  permutation_upper _ _ _ [34,132,257,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37782

def r42985 : Route 9 := (fun mask => (mask,id))

def c42985 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42985 : Upper (D 6) (R 6) [34,132,257,48] 13 := by
  apply FastRouting.sound _ _ [34,132,257,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42985 c42985
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42985_3
  · exact m42985_5
  · exact m42985_6
  · exact m42985_9
  · exact m42985_10
  · exact m42985_12
  · exact u37796
  · exact u37797
  · exact u37798
  · exact u37799

theorem m42986_6 : Upper (D 6) (R 6) [34,132,257,65,6] 13 :=
  permutation_upper _ _ _ [34,132,257,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37760

theorem m42986_10 : Upper (D 6) (R 6) [34,132,257,65,10] 13 :=
  permutation_upper _ _ _ [34,132,257,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37776

theorem m42986_12 : Upper (D 6) (R 6) [34,132,257,65,12] 13 :=
  permutation_upper _ _ _ [34,132,257,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37783

theorem m42986_34 : Upper (D 6) (R 6) [34,132,257,65,34] 13 :=
  permutation_upper _ _ _ [34,132,257,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37790

theorem m42986_36 : Upper (D 6) (R 6) [34,132,257,65,36] 13 :=
  permutation_upper _ _ _ [34,132,257,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37793

theorem m42986_40 : Upper (D 6) (R 6) [34,132,257,65,40] 13 :=
  permutation_upper _ _ _ [34,132,257,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37796

def r42986 : Route 9 := (fun mask => (mask,id))

def c42986 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42986 : Upper (D 6) (R 6) [34,132,257,65] 13 := by
  apply FastRouting.sound _ _ [34,132,257,65] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r42986 c42986
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42986_6
  · exact m42986_10
  · exact m42986_12
  · exact m42986_34
  · exact m42986_36
  · exact m42986_40
  · exact u37800
  · exact u37801
  · exact u37802
  · exact u37803

theorem m42987_5 : Upper (D 6) (R 6) [34,132,257,66,5] 13 :=
  permutation_upper _ _ _ [34,132,257,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37755

theorem m42987_9 : Upper (D 6) (R 6) [34,132,257,66,9] 13 :=
  permutation_upper _ _ _ [34,132,257,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37768

theorem m42987_12 : Upper (D 6) (R 6) [34,132,257,66,12] 13 :=
  permutation_upper _ _ _ [34,132,257,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37784

theorem m42987_33 : Upper (D 6) (R 6) [34,132,257,66,33] 13 :=
  permutation_upper _ _ _ [34,132,257,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37787

theorem m42987_36 : Upper (D 6) (R 6) [34,132,257,66,36] 13 :=
  permutation_upper _ _ _ [34,132,257,36,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37794

theorem m42987_40 : Upper (D 6) (R 6) [34,132,257,66,40] 13 :=
  permutation_upper _ _ _ [34,132,257,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37797

theorem m42987_65 : Upper (D 6) (R 6) [34,132,257,66,65] 13 :=
  permutation_upper _ _ _ [34,132,257,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37800

def r42987 : Route 9 := (fun mask => (mask,id))

def c42987 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42987 : Upper (D 6) (R 6) [34,132,257,66] 13 := by
  apply FastRouting.sound _ _ [34,132,257,66] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r42987 c42987
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42987_5
  · exact m42987_9
  · exact m42987_12
  · exact m42987_33
  · exact m42987_36
  · exact m42987_40
  · exact m42987_65
  · exact u37804
  · exact u37805
  · exact u37806

theorem m42988_3 : Upper (D 6) (R 6) [34,132,257,68,3] 13 :=
  permutation_upper _ _ _ [34,132,257,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37750

theorem m42988_9 : Upper (D 6) (R 6) [34,132,257,68,9] 13 :=
  permutation_upper _ _ _ [34,132,257,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37769

theorem m42988_10 : Upper (D 6) (R 6) [34,132,257,68,10] 13 :=
  permutation_upper _ _ _ [34,132,257,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37777

theorem m42988_33 : Upper (D 6) (R 6) [34,132,257,68,33] 13 :=
  permutation_upper _ _ _ [34,132,257,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37788

theorem m42988_34 : Upper (D 6) (R 6) [34,132,257,68,34] 13 :=
  permutation_upper _ _ _ [34,132,257,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37791

theorem m42988_40 : Upper (D 6) (R 6) [34,132,257,68,40] 13 :=
  permutation_upper _ _ _ [34,132,257,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37798

theorem m42988_65 : Upper (D 6) (R 6) [34,132,257,68,65] 13 :=
  permutation_upper _ _ _ [34,132,257,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37801

theorem m42988_66 : Upper (D 6) (R 6) [34,132,257,68,66] 13 :=
  permutation_upper _ _ _ [34,132,257,66,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37804

def r42988 : Route 9 := (fun mask => (mask,id))

def c42988 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42988 : Upper (D 6) (R 6) [34,132,257,68] 13 := by
  apply FastRouting.sound _ _ [34,132,257,68] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r42988 c42988
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42988_3
  · exact m42988_9
  · exact m42988_10
  · exact m42988_33
  · exact m42988_34
  · exact m42988_40
  · exact m42988_65
  · exact m42988_66
  · exact u37807
  · exact u37808

theorem m42989_3 : Upper (D 6) (R 6) [34,132,257,80,3] 13 :=
  permutation_upper _ _ _ [34,132,257,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37751

theorem m42989_5 : Upper (D 6) (R 6) [34,132,257,80,5] 13 :=
  permutation_upper _ _ _ [34,132,257,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37756

theorem m42989_6 : Upper (D 6) (R 6) [34,132,257,80,6] 13 :=
  permutation_upper _ _ _ [34,132,257,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37761

theorem m42989_9 : Upper (D 6) (R 6) [34,132,257,80,9] 13 :=
  permutation_upper _ _ _ [34,132,257,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37770

theorem m42989_10 : Upper (D 6) (R 6) [34,132,257,80,10] 13 :=
  permutation_upper _ _ _ [34,132,257,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37778

theorem m42989_12 : Upper (D 6) (R 6) [34,132,257,80,12] 13 :=
  permutation_upper _ _ _ [34,132,257,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37785

theorem m42989_33 : Upper (D 6) (R 6) [34,132,257,80,33] 13 :=
  permutation_upper _ _ _ [34,132,257,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37789

theorem m42989_34 : Upper (D 6) (R 6) [34,132,257,80,34] 13 :=
  permutation_upper _ _ _ [34,132,257,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37792

theorem m42989_36 : Upper (D 6) (R 6) [34,132,257,80,36] 13 :=
  permutation_upper _ _ _ [34,132,257,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37795

theorem m42989_40 : Upper (D 6) (R 6) [34,132,257,80,40] 13 :=
  permutation_upper _ _ _ [34,132,257,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37799

theorem m42989_65 : Upper (D 6) (R 6) [34,132,257,80,65] 13 :=
  permutation_upper _ _ _ [34,132,257,65,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37802

theorem m42989_66 : Upper (D 6) (R 6) [34,132,257,80,66] 13 :=
  permutation_upper _ _ _ [34,132,257,66,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37805

theorem m42989_68 : Upper (D 6) (R 6) [34,132,257,80,68] 13 :=
  permutation_upper _ _ _ [34,132,257,68,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37807

def r42989 : Route 9 := (fun mask => (mask,id))

def c42989 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42989 : Upper (D 6) (R 6) [34,132,257,80] 13 := by
  apply FastRouting.sound _ _ [34,132,257,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r42989 c42989
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42989_3
  · exact m42989_5
  · exact m42989_6
  · exact m42989_9
  · exact m42989_10
  · exact m42989_12
  · exact m42989_33
  · exact m42989_34
  · exact m42989_36
  · exact m42989_40
  · exact m42989_65
  · exact m42989_66
  · exact m42989_68
  · exact u37809
  · exact u37810

theorem m42990_3 : Upper (D 6) (R 6) [34,132,257,96,3] 13 :=
  permutation_upper _ _ _ [34,132,257,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37752

theorem m42990_5 : Upper (D 6) (R 6) [34,132,257,96,5] 13 :=
  permutation_upper _ _ _ [34,132,257,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37757

theorem m42990_6 : Upper (D 6) (R 6) [34,132,257,96,6] 13 :=
  permutation_upper _ _ _ [34,132,257,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37762

theorem m42990_9 : Upper (D 6) (R 6) [34,132,257,96,9] 13 :=
  permutation_upper _ _ _ [34,132,257,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37771

theorem m42990_10 : Upper (D 6) (R 6) [34,132,257,96,10] 13 :=
  permutation_upper _ _ _ [34,132,257,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37779

theorem m42990_12 : Upper (D 6) (R 6) [34,132,257,96,12] 13 :=
  permutation_upper _ _ _ [34,132,257,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37786

theorem m42990_65 : Upper (D 6) (R 6) [34,132,257,96,65] 13 :=
  permutation_upper _ _ _ [34,132,257,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37803

theorem m42990_66 : Upper (D 6) (R 6) [34,132,257,96,66] 13 :=
  permutation_upper _ _ _ [34,132,257,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37806

theorem m42990_68 : Upper (D 6) (R 6) [34,132,257,96,68] 13 :=
  permutation_upper _ _ _ [34,132,257,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37808

theorem m42990_72 : Upper (D 6) (R 6) [34,132,257,96,72] 13 :=
  permutation_upper _ _ _ [34,132,257,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37810

def r42990 : Route 9 := (fun mask => (mask,id))

def c42990 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42990 : Upper (D 6) (R 6) [34,132,257,96] 13 := by
  apply FastRouting.sound _ _ [34,132,257,96] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42990 c42990
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42990_3
  · exact m42990_5
  · exact m42990_6
  · exact m42990_9
  · exact m42990_10
  · exact m42990_12
  · exact m42990_65
  · exact m42990_66
  · exact m42990_68
  · exact m42990_72

def r42991 : Route 9 := (fun mask => (mask,id))

def c42991 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42991 : Upper (D 6) (R 6) [34,132,258,5] 13 := by
  apply FastRouting.sound _ _ [34,132,258,5] 13 (by decide) (choices 2) [9,33,40,65,72,96] r42991 c42991
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37811
  · exact u37812
  · exact u37813
  · exact u37814
  · exact u37815
  · exact u37816

theorem m42992_5 : Upper (D 6) (R 6) [34,132,258,17,5] 13 :=
  permutation_upper _ _ _ [34,132,258,5,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37811

def r42992 : Route 9 := (fun mask => (mask,id))

def c42992 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42992 : Upper (D 6) (R 6) [34,132,258,17] 13 := by
  apply FastRouting.sound _ _ [34,132,258,17] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r42992 c42992
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42992_5
  · exact u37817
  · exact u37818
  · exact u37819
  · exact u37820
  · exact u37821
  · exact u37822
  · exact u37823
  · exact u37824
  · exact u37825

theorem m42993_9 : Upper (D 6) (R 6) [34,132,258,20,9] 13 :=
  permutation_upper _ _ _ [34,132,258,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37818

def r42993 : Route 9 := (fun mask => (mask,id))

def c42993 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42993 : Upper (D 6) (R 6) [34,132,258,20] 13 := by
  apply FastRouting.sound _ _ [34,132,258,20] 13 (by decide) (choices 2) [9,33,40,65,72,96] r42993 c42993
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42993_9
  · exact u37826
  · exact u37827
  · exact u37828
  · exact u37829
  · exact u37830

def b42994 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 262 41 93 125 93 221 349), lower := (rows 35 134 262 41 16 32 64 128 256), losses := [] }

theorem u42994 : Upper (D 6) (R 6) [34,132,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42995_9 : Upper (D 6) (R 6) [34,132,258,36,9] 13 :=
  permutation_upper _ _ _ [34,132,258,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37820

def r42995 : Route 9 := (fun mask => (mask,id))

def c42995 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42995 : Upper (D 6) (R 6) [34,132,258,36] 13 := by
  apply FastRouting.sound _ _ [34,132,258,36] 13 (by decide) (choices 2) [9,65,72] r42995 c42995
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m42995_9
  · exact u37834
  · exact u37835

theorem m42996_5 : Upper (D 6) (R 6) [34,132,258,48,5] 13 :=
  permutation_upper _ _ _ [34,132,258,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37813

theorem m42996_9 : Upper (D 6) (R 6) [34,132,258,48,9] 13 :=
  permutation_upper _ _ _ [34,132,258,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37821

theorem m42996_12 : Upper (D 6) (R 6) [34,132,258,48,12] 13 :=
  permutation_upper _ _ _ [34,132,258,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37827

def r42996 : Route 9 := (fun mask => (mask,id))

def c42996 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42996 : Upper (D 6) (R 6) [34,132,258,48] 13 := by
  apply FastRouting.sound _ _ [34,132,258,48] 13 (by decide) (choices 2) [5,9,12,65,68,72] r42996 c42996
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42996_5
  · exact m42996_9
  · exact m42996_12
  · exact u37836
  · exact u37837
  · exact u37838

theorem m42997_5 : Upper (D 6) (R 6) [34,132,258,65,5] 13 :=
  permutation_upper _ _ _ [34,132,258,5,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37814

theorem m42997_9 : Upper (D 6) (R 6) [34,132,258,65,9] 13 :=
  permutation_upper _ _ _ [34,132,258,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37822

theorem m42997_12 : Upper (D 6) (R 6) [34,132,258,65,12] 13 :=
  permutation_upper _ _ _ [34,132,258,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37828

theorem m42997_33 : Upper (D 6) (R 6) [34,132,258,65,33] 13 :=
  permutation_upper _ _ _ [34,132,258,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37831

theorem m42997_36 : Upper (D 6) (R 6) [34,132,258,65,36] 13 :=
  permutation_upper _ _ _ [34,132,258,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37834

theorem m42997_40 : Upper (D 6) (R 6) [34,132,258,65,40] 13 :=
  permutation_upper _ _ _ [34,132,258,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37836

def r42997 : Route 9 := (fun mask => (mask,id))

def c42997 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42997 : Upper (D 6) (R 6) [34,132,258,65] 13 := by
  apply FastRouting.sound _ _ [34,132,258,65] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r42997 c42997
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42997_5
  · exact m42997_9
  · exact m42997_12
  · exact m42997_33
  · exact m42997_36
  · exact m42997_40
  · exact u37839
  · exact u37840
  · exact u37841
  · exact u37842

theorem m42998_9 : Upper (D 6) (R 6) [34,132,258,68,9] 13 :=
  permutation_upper _ _ _ [34,132,258,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37823

theorem m42998_33 : Upper (D 6) (R 6) [34,132,258,68,33] 13 :=
  permutation_upper _ _ _ [34,132,258,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37832

theorem m42998_40 : Upper (D 6) (R 6) [34,132,258,68,40] 13 :=
  permutation_upper _ _ _ [34,132,258,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37837

theorem m42998_65 : Upper (D 6) (R 6) [34,132,258,68,65] 13 :=
  permutation_upper _ _ _ [34,132,258,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37840

def r42998 : Route 9 := (fun mask => (mask,id))

def c42998 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42998 : Upper (D 6) (R 6) [34,132,258,68] 13 := by
  apply FastRouting.sound _ _ [34,132,258,68] 13 (by decide) (choices 2) [9,33,40,65,72,96] r42998 c42998
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42998_9
  · exact m42998_33
  · exact m42998_40
  · exact m42998_65
  · exact u37843
  · exact u37844

theorem m42999_5 : Upper (D 6) (R 6) [34,132,258,80,5] 13 :=
  permutation_upper _ _ _ [34,132,258,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37815

theorem m42999_9 : Upper (D 6) (R 6) [34,132,258,80,9] 13 :=
  permutation_upper _ _ _ [34,132,258,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37824

theorem m42999_12 : Upper (D 6) (R 6) [34,132,258,80,12] 13 :=
  permutation_upper _ _ _ [34,132,258,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37829

theorem m42999_33 : Upper (D 6) (R 6) [34,132,258,80,33] 13 :=
  permutation_upper _ _ _ [34,132,258,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37833

theorem m42999_36 : Upper (D 6) (R 6) [34,132,258,80,36] 13 :=
  permutation_upper _ _ _ [34,132,258,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37835

theorem m42999_40 : Upper (D 6) (R 6) [34,132,258,80,40] 13 :=
  permutation_upper _ _ _ [34,132,258,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37838

theorem m42999_65 : Upper (D 6) (R 6) [34,132,258,80,65] 13 :=
  permutation_upper _ _ _ [34,132,258,65,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37841

theorem m42999_68 : Upper (D 6) (R 6) [34,132,258,80,68] 13 :=
  permutation_upper _ _ _ [34,132,258,68,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37843

def r42999 : Route 9 := (fun mask => (mask,id))

def c42999 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42999 : Upper (D 6) (R 6) [34,132,258,80] 13 := by
  apply FastRouting.sound _ _ [34,132,258,80] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r42999 c42999
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42999_5
  · exact m42999_9
  · exact m42999_12
  · exact m42999_33
  · exact m42999_36
  · exact m42999_40
  · exact m42999_65
  · exact m42999_68
  · exact u37845
  · exact u37846

theorem m43000_5 : Upper (D 6) (R 6) [34,132,258,96,5] 13 :=
  permutation_upper _ _ _ [34,132,258,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37816

theorem m43000_9 : Upper (D 6) (R 6) [34,132,258,96,9] 13 :=
  permutation_upper _ _ _ [34,132,258,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37825

theorem m43000_12 : Upper (D 6) (R 6) [34,132,258,96,12] 13 :=
  permutation_upper _ _ _ [34,132,258,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37830

theorem m43000_65 : Upper (D 6) (R 6) [34,132,258,96,65] 13 :=
  permutation_upper _ _ _ [34,132,258,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37842

theorem m43000_68 : Upper (D 6) (R 6) [34,132,258,96,68] 13 :=
  permutation_upper _ _ _ [34,132,258,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37844

theorem m43000_72 : Upper (D 6) (R 6) [34,132,258,96,72] 13 :=
  permutation_upper _ _ _ [34,132,258,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37846

def r43000 : Route 9 := (fun mask => (mask,id))

def c43000 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43000 : Upper (D 6) (R 6) [34,132,258,96] 13 := by
  apply FastRouting.sound _ _ [34,132,258,96] 13 (by decide) (choices 2) [5,9,12,65,68,72] r43000 c43000
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43000_5
  · exact m43000_9
  · exact m43000_12
  · exact m43000_65
  · exact m43000_68
  · exact m43000_72

def b43001 : PairBound 9 := { available := 117, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 268 11 117 117 117 245 373), lower := (rows 35 134 268 11 16 32 64 128 256), losses := [] }

theorem u43001 : Upper (D 6) (R 6) [34,132,264,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43002 : Route 9 := (fun mask => (mask,id))

def c43002 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43002 : Upper (D 6) (R 6) [34,132,264,5] 13 := by
  apply FastRouting.sound _ _ [34,132,264,5] 13 (by decide) (choices 2) [3,33,34,65,66,96] r43002 c43002
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37847
  · exact u37848
  · exact u37849
  · exact u37850
  · exact u37851
  · exact u37852

def b43003 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 268 14 113 113 113 241 369), lower := (rows 35 134 268 14 16 32 64 128 256), losses := [] }

theorem u43003 : Upper (D 6) (R 6) [34,132,264,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43004 : Route 9 := (fun mask => (mask,id))

def c43004 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43004 : Upper (D 6) (R 6) [34,132,264,17] 13 := by
  apply FastRouting.sound _ _ [34,132,264,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43004 c43004
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37853
  · exact u37854
  · exact u37855
  · exact u37856
  · exact u37857
  · exact u37858
  · exact u37859
  · exact u37860
  · exact u37861
  · exact u37862

def r43005 : Route 9 := (fun mask => (mask,id))

def c43005 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43005 : Upper (D 6) (R 6) [34,132,264,18] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43005 c43005
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37863
  · exact u37864
  · exact u37865
  · exact u37866
  · exact u37867
  · exact u37868

def r43006 : Route 9 := (fun mask => (mask,id))

def c43006 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43006 : Upper (D 6) (R 6) [34,132,264,20] 13 := by
  apply FastRouting.sound _ _ [34,132,264,20] 13 (by decide) (choices 2) [3,33,34,65,66,96] r43006 c43006
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37869
  · exact u37870
  · exact u37871
  · exact u37872
  · exact u37873
  · exact u37874

def b43007 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 268 41 87 119 87 215 343), lower := (rows 35 134 268 41 16 32 64 128 256), losses := [] }

theorem u43007 : Upper (D 6) (R 6) [34,132,264,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43008 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 134 268 42 85 117 85 213 341), lower := (rows 35 134 268 42 16 32 64 128 256), losses := [] }

theorem u43008 : Upper (D 6) (R 6) [34,132,264,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43009 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 134 268 44 83 115 83 211 339), lower := (rows 35 134 268 44 16 32 64 128 256), losses := [] }

theorem u43009 : Upper (D 6) (R 6) [34,132,264,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43010 : Route 9 := (fun mask => (mask,id))

def c43010 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43010 : Upper (D 6) (R 6) [34,132,264,48] 13 := by
  apply FastRouting.sound _ _ [34,132,264,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43010 c43010
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37875
  · exact u37876
  · exact u37877
  · exact u37878
  · exact u37879
  · exact u37880

def r43011 : Route 9 := (fun mask => (mask,id))

def c43011 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43011 : Upper (D 6) (R 6) [34,132,264,65] 13 := by
  apply FastRouting.sound _ _ [34,132,264,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43011 c43011
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37881
  · exact u37882
  · exact u37883
  · exact u37884
  · exact u37885
  · exact u37886
  · exact u37887
  · exact u37888
  · exact u37889
  · exact u37890

def r43012 : Route 9 := (fun mask => (mask,id))

def c43012 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43012 : Upper (D 6) (R 6) [34,132,264,66] 13 := by
  apply FastRouting.sound _ _ [34,132,264,66] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43012 c43012
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37891
  · exact u37892
  · exact u37893
  · exact u37894
  · exact u37895
  · exact u37896

def r43013 : Route 9 := (fun mask => (mask,id))

def c43013 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43013 : Upper (D 6) (R 6) [34,132,264,68] 13 := by
  apply FastRouting.sound _ _ [34,132,264,68] 13 (by decide) (choices 2) [3,33,34,65,66,96] r43013 c43013
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37897
  · exact u37898
  · exact u37899
  · exact u37900
  · exact u37901
  · exact u37902

def r43014 : Route 9 := (fun mask => (mask,id))

def c43014 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43014 : Upper (D 6) (R 6) [34,132,264,80] 13 := by
  apply FastRouting.sound _ _ [34,132,264,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43014 c43014
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37903
  · exact u37904
  · exact u37905
  · exact u37906
  · exact u37907
  · exact u37908
  · exact u37909
  · exact u37910
  · exact u37911
  · exact u37912

def r43015 : Route 9 := (fun mask => (mask,id))

def c43015 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43015 : Upper (D 6) (R 6) [34,132,264,96] 13 := by
  apply FastRouting.sound _ _ [34,132,264,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43015 c43015
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37913
  · exact u37914
  · exact u37915
  · exact u37916
  · exact u37917
  · exact u37918

def b43016 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 292 11 93 125 93 221 349), lower := (rows 35 134 292 11 16 32 64 128 256), losses := [] }

theorem u43016 : Upper (D 6) (R 6) [34,132,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43017_3 : Upper (D 6) (R 6) [34,132,288,5,3] 13 :=
  permutation_upper _ _ _ [34,132,288,3,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37919

def r43017 : Route 9 := (fun mask => (mask,id))

def c43017 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43017 : Upper (D 6) (R 6) [34,132,288,5] 13 := by
  apply FastRouting.sound _ _ [34,132,288,5] 13 (by decide) (choices 2) [3,9,10,65,66,72] r43017 c43017
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43017_3
  · exact u37925
  · exact u37926
  · exact u37927
  · exact u37928
  · exact u37929

def b43018 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 292 14 89 121 89 217 345), lower := (rows 35 134 292 14 16 32 64 128 256), losses := [] }

theorem u43018 : Upper (D 6) (R 6) [34,132,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43019_3 : Upper (D 6) (R 6) [34,132,288,17,3] 13 :=
  permutation_upper _ _ _ [34,132,288,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37920

theorem m43019_5 : Upper (D 6) (R 6) [34,132,288,17,5] 13 :=
  permutation_upper _ _ _ [34,132,288,5,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37925

theorem m43019_6 : Upper (D 6) (R 6) [34,132,288,17,6] 13 :=
  permutation_upper _ _ _ [34,132,288,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37930

def r43019 : Route 9 := (fun mask => (mask,id))

def c43019 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43019 : Upper (D 6) (R 6) [34,132,288,17] 13 := by
  apply FastRouting.sound _ _ [34,132,288,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43019 c43019
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43019_3
  · exact m43019_5
  · exact m43019_6
  · exact u37933
  · exact u37934
  · exact u37935
  · exact u37936
  · exact u37937
  · exact u37938
  · exact u37939

#print axioms u43019
end Delivery.IrregularNine14.P06
