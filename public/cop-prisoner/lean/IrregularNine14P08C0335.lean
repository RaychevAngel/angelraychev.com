import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0172
import IrregularNine14P08C0173
import IrregularNine14P08C0174
import IrregularNine14P08C0175
import IrregularNine14P08C0176
import IrregularNine14P08C0177
import IrregularNine14P08C0178
import IrregularNine14P08C0179
import IrregularNine14P08C0180

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m20100_5 : Upper (D 8) (R 8) [66,33,160,384,5] 13 :=
  permutation_upper _ _ _ [66,33,9,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10335

theorem m20100_9 : Upper (D 8) (R 8) [66,33,160,384,9] 13 :=
  permutation_upper _ _ _ [66,33,9,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10360

theorem m20100_12 : Upper (D 8) (R 8) [66,33,160,384,12] 13 :=
  permutation_upper _ _ _ [66,33,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10411

theorem m20100_33 : Upper (D 8) (R 8) [66,33,160,384,33] 13 :=
  permutation_upper _ _ _ [66,33,33,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10454

theorem m20100_36 : Upper (D 8) (R 8) [66,33,160,384,36] 13 :=
  permutation_upper _ _ _ [66,33,40,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10520

theorem m20100_40 : Upper (D 8) (R 8) [66,33,160,384,40] 13 :=
  permutation_upper _ _ _ [66,33,40,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10555

theorem m20100_65 : Upper (D 8) (R 8) [66,33,160,384,65] 13 :=
  permutation_upper _ _ _ [66,33,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10567

theorem m20100_68 : Upper (D 8) (R 8) [66,33,160,384,68] 13 :=
  permutation_upper _ _ _ [66,33,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10589

theorem m20100_72 : Upper (D 8) (R 8) [66,33,160,384,72] 13 :=
  permutation_upper _ _ _ [66,33,72,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10601

theorem m20100_96 : Upper (D 8) (R 8) [66,33,160,384,96] 13 :=
  permutation_upper _ _ _ [66,33,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10611

def r20100 : Route 9 := (fun mask => (mask,id))

def c20100 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20100 : Upper (D 8) (R 8) [66,33,160,384] 13 := by
  apply FastRouting.sound _ _ [66,33,160,384] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r20100 c20100
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20100_5
  · exact m20100_9
  · exact m20100_12
  · exact m20100_33
  · exact m20100_36
  · exact m20100_40
  · exact m20100_65
  · exact m20100_68
  · exact m20100_72
  · exact m20100_96

def b20101 : PairBound 9 := { available := 188, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 196 265 188 188 252 188 444), lower := (rows 67 35 196 265 16 32 64 128 256), losses := [] }

theorem u20101 : Upper (D 8) (R 8) [66,33,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20102_9 : Upper (D 8) (R 8) [66,33,192,260,9] 13 :=
  permutation_upper _ _ _ [66,33,9,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10348

theorem m20102_33 : Upper (D 8) (R 8) [66,33,192,260,33] 13 :=
  permutation_upper _ _ _ [66,33,33,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10456

theorem m20102_40 : Upper (D 8) (R 8) [66,33,192,260,40] 13 :=
  permutation_upper _ _ _ [66,33,40,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10543

theorem m20102_129 : Upper (D 8) (R 8) [66,33,192,260,129] 13 :=
  permutation_upper _ _ _ [66,33,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10624

theorem m20102_136 : Upper (D 8) (R 8) [66,33,192,260,136] 13 :=
  permutation_upper _ _ _ [66,33,136,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10641

theorem m20102_160 : Upper (D 8) (R 8) [66,33,192,260,160] 13 :=
  permutation_upper _ _ _ [66,33,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10649

def r20102 : Route 9 := (fun mask => (mask,id))

def c20102 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20102 : Upper (D 8) (R 8) [66,33,192,260] 13 := by
  apply FastRouting.sound _ _ [66,33,192,260] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20102 c20102
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20102_9
  · exact m20102_33
  · exact m20102_40
  · exact m20102_129
  · exact m20102_136
  · exact m20102_160

theorem m20103_5 : Upper (D 8) (R 8) [66,33,192,272,5] 13 :=
  permutation_upper _ _ _ [66,33,9,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10339

theorem m20103_9 : Upper (D 8) (R 8) [66,33,192,272,9] 13 :=
  permutation_upper _ _ _ [66,33,9,260,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10343

theorem m20103_12 : Upper (D 8) (R 8) [66,33,192,272,12] 13 :=
  permutation_upper _ _ _ [66,33,24,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10413

theorem m20103_33 : Upper (D 8) (R 8) [66,33,192,272,33] 13 :=
  permutation_upper _ _ _ [66,33,33,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10455

theorem m20103_36 : Upper (D 8) (R 8) [66,33,192,272,36] 13 :=
  permutation_upper _ _ _ [66,33,40,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10525

theorem m20103_40 : Upper (D 8) (R 8) [66,33,192,272,40] 13 :=
  permutation_upper _ _ _ [66,33,40,260,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10536

theorem m20103_129 : Upper (D 8) (R 8) [66,33,192,272,129] 13 :=
  permutation_upper _ _ _ [66,33,129,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10623

theorem m20103_132 : Upper (D 8) (R 8) [66,33,192,272,132] 13 :=
  permutation_upper _ _ _ [66,33,136,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10634

theorem m20103_136 : Upper (D 8) (R 8) [66,33,192,272,136] 13 :=
  permutation_upper _ _ _ [66,33,136,260,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10639

theorem m20103_160 : Upper (D 8) (R 8) [66,33,192,272,160] 13 :=
  permutation_upper _ _ _ [66,33,160,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10648

def r20103 : Route 9 := (fun mask => (mask,id))

def c20103 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20103 : Upper (D 8) (R 8) [66,33,192,272] 13 := by
  apply FastRouting.sound _ _ [66,33,192,272] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r20103 c20103
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20103_5
  · exact m20103_9
  · exact m20103_12
  · exact m20103_33
  · exact m20103_36
  · exact m20103_40
  · exact m20103_129
  · exact m20103_132
  · exact m20103_136
  · exact m20103_160

theorem m20104_5 : Upper (D 8) (R 8) [66,33,192,288,5] 13 :=
  permutation_upper _ _ _ [66,33,9,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10340

theorem m20104_9 : Upper (D 8) (R 8) [66,33,192,288,9] 13 :=
  permutation_upper _ _ _ [66,33,9,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10353

theorem m20104_12 : Upper (D 8) (R 8) [66,33,192,288,12] 13 :=
  permutation_upper _ _ _ [66,33,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10414

theorem m20104_33 : Upper (D 8) (R 8) [66,33,192,288,33] 13 :=
  permutation_upper _ _ _ [66,33,33,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10457

theorem m20104_36 : Upper (D 8) (R 8) [66,33,192,288,36] 13 :=
  permutation_upper _ _ _ [66,33,40,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10526

theorem m20104_40 : Upper (D 8) (R 8) [66,33,192,288,40] 13 :=
  permutation_upper _ _ _ [66,33,40,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10546

theorem m20104_129 : Upper (D 8) (R 8) [66,33,192,288,129] 13 :=
  permutation_upper _ _ _ [66,33,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10625

theorem m20104_132 : Upper (D 8) (R 8) [66,33,192,288,132] 13 :=
  permutation_upper _ _ _ [66,33,136,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10635

theorem m20104_136 : Upper (D 8) (R 8) [66,33,192,288,136] 13 :=
  permutation_upper _ _ _ [66,33,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10643

theorem m20104_160 : Upper (D 8) (R 8) [66,33,192,288,160] 13 :=
  permutation_upper _ _ _ [66,33,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10650

def r20104 : Route 9 := (fun mask => (mask,id))

def c20104 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20104 : Upper (D 8) (R 8) [66,33,192,288] 13 := by
  apply FastRouting.sound _ _ [66,33,192,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r20104 c20104
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20104_5
  · exact m20104_9
  · exact m20104_12
  · exact m20104_33
  · exact m20104_36
  · exact m20104_40
  · exact m20104_129
  · exact m20104_132
  · exact m20104_136
  · exact m20104_160

theorem m20105_5 : Upper (D 8) (R 8) [66,33,192,384,5] 13 :=
  permutation_upper _ _ _ [66,33,9,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10341

theorem m20105_9 : Upper (D 8) (R 8) [66,33,192,384,9] 13 :=
  permutation_upper _ _ _ [66,33,9,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10361

theorem m20105_12 : Upper (D 8) (R 8) [66,33,192,384,12] 13 :=
  permutation_upper _ _ _ [66,33,24,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10415

theorem m20105_33 : Upper (D 8) (R 8) [66,33,192,384,33] 13 :=
  permutation_upper _ _ _ [66,33,33,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10458

theorem m20105_36 : Upper (D 8) (R 8) [66,33,192,384,36] 13 :=
  permutation_upper _ _ _ [66,33,40,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10527

theorem m20105_40 : Upper (D 8) (R 8) [66,33,192,384,40] 13 :=
  permutation_upper _ _ _ [66,33,40,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10556

def r20105 : Route 9 := (fun mask => (mask,id))

def c20105 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20105 : Upper (D 8) (R 8) [66,33,192,384] 13 := by
  apply FastRouting.sound _ _ [66,33,192,384] 13 (by decide) (choices 2) [5,9,12,33,36,40] r20105 c20105
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20105_5
  · exact m20105_9
  · exact m20105_12
  · exact m20105_33
  · exact m20105_36
  · exact m20105_40

def b20106 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 38 13 25 496 480 480 480 480), lower := (rows 67 38 13 25 16 32 64 128 256), losses := [] }

theorem u20106 : Upper (D 8) (R 8) [66,36,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20107 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 41 496 496 496 496 496), lower := (rows 67 38 13 41 16 32 64 128 256), losses := [] }

theorem u20107 : Upper (D 8) (R 8) [66,36,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20108 : Route 9 := (fun mask => (mask,id))

def c20108 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20108 : Upper (D 8) (R 8) [66,36,9,48] 13 := by
  apply FastRouting.sound _ _ [66,36,9,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20108 c20108
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10651
  · exact u10652
  · exact u10653
  · exact u10654
  · exact u10655
  · exact u10656
  · exact u10657
  · exact u10658
  · exact u10659
  · exact u10660

def b20109 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 38 13 73 432 432 496 432 432), lower := (rows 67 38 13 73 16 32 64 128 256), losses := [] }

theorem u20109 : Upper (D 8) (R 8) [66,36,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20110 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 88 433 417 481 417 417), lower := (rows 67 38 13 88 16 32 64 128 256), losses := [] }

theorem u20110 : Upper (D 8) (R 8) [66,36,9,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20110 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20111 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 104 433 433 497 433 433), lower := (rows 67 38 13 104 16 32 64 128 256), losses := [] }

theorem u20111 : Upper (D 8) (R 8) [66,36,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20112 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 38 13 137 496 496 496 496 496), lower := (rows 67 38 13 137 16 32 64 128 256), losses := [] }

theorem u20112 : Upper (D 8) (R 8) [66,36,9,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20113 : Route 9 := (fun mask => (mask,id))

def c20113 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20113 : Upper (D 8) (R 8) [66,36,9,144] 13 := by
  apply FastRouting.sound _ _ [66,36,9,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20113 c20113
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10661
  · exact u10662
  · exact u10663
  · exact u10664
  · exact u10665
  · exact u10666
  · exact u10667
  · exact u10668
  · exact u10669
  · exact u10670

def r20114 : Route 9 := (fun mask => (mask,id))

def c20114 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20114 : Upper (D 8) (R 8) [66,36,9,160] 13 := by
  apply FastRouting.sound _ _ [66,36,9,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20114 c20114
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10671
  · exact u10672
  · exact u10673
  · exact u10674
  · exact u10675
  · exact u10676
  · exact u10677
  · exact u10678
  · exact u10679
  · exact u10680

def b20115 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 200 433 433 497 433 433), lower := (rows 67 38 13 200 16 32 64 128 256), losses := [] }

theorem u20115 : Upper (D 8) (R 8) [66,36,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20116 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 38 13 265 240 240 240 240 496), lower := (rows 67 38 13 265 16 32 64 128 256), losses := [] }

theorem u20116 : Upper (D 8) (R 8) [66,36,9,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20117 : Route 9 := (fun mask => (mask,id))

def c20117 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20117 : Upper (D 8) (R 8) [66,36,9,272] 13 := by
  apply FastRouting.sound _ _ [66,36,9,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20117 c20117
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10681
  · exact u10682
  · exact u10683
  · exact u10684
  · exact u10685
  · exact u10686

def r20118 : Route 9 := (fun mask => (mask,id))

def c20118 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20118 : Upper (D 8) (R 8) [66,36,9,288] 13 := by
  apply FastRouting.sound _ _ [66,36,9,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20118 c20118
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10687
  · exact u10688
  · exact u10689
  · exact u10690
  · exact u10691
  · exact u10692

def b20119 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 328 177 177 241 177 433), lower := (rows 67 38 13 328 16 32 64 128 256), losses := [] }

theorem u20119 : Upper (D 8) (R 8) [66,36,9,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20120 : Route 9 := (fun mask => (mask,id))

def c20120 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20120 : Upper (D 8) (R 8) [66,36,9,384] 13 := by
  apply FastRouting.sound _ _ [66,36,9,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20120 c20120
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10693
  · exact u10694
  · exact u10695
  · exact u10696
  · exact u10697
  · exact u10698

def r20121 : Route 9 := (fun mask => (mask,id))

def c20121 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20121 : Upper (D 8) (R 8) [66,36,24,33] 13 := by
  apply FastRouting.sound _ _ [66,36,24,33] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20121 c20121
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10699
  · exact u10700
  · exact u10701
  · exact u10702
  · exact u10703
  · exact u10704
  · exact u10705
  · exact u10706
  · exact u10707
  · exact u10708

def b20122 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 28 73 433 417 481 417 417), lower := (rows 67 38 28 73 16 32 64 128 256), losses := [] }

theorem u20122 : Upper (D 8) (R 8) [66,36,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20123 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 28 104 433 417 481 417 417), lower := (rows 67 38 28 104 16 32 64 128 256), losses := [] }

theorem u20123 : Upper (D 8) (R 8) [66,36,24,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20124_33 : Upper (D 8) (R 8) [66,36,24,129,33] 13 :=
  permutation_upper _ _ _ [66,36,24,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10702

theorem m20124_65 : Upper (D 8) (R 8) [66,36,24,129,65] 13 :=
  permutation_upper _ _ _ [66,36,24,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10709

theorem m20124_96 : Upper (D 8) (R 8) [66,36,24,129,96] 13 :=
  permutation_upper _ _ _ [66,36,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10714

def r20124 : Route 9 := (fun mask => (mask,id))

def c20124 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20124 : Upper (D 8) (R 8) [66,36,24,129] 13 := by
  apply FastRouting.sound _ _ [66,36,24,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20124 c20124
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20124_33
  · exact m20124_65
  · exact m20124_96
  · exact u10719
  · exact u10720
  · exact u10721
  · exact u10722
  · exact u10723
  · exact u10724
  · exact u10725

theorem m20125_33 : Upper (D 8) (R 8) [66,36,24,160,33] 13 :=
  permutation_upper _ _ _ [66,36,24,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10703

theorem m20125_65 : Upper (D 8) (R 8) [66,36,24,160,65] 13 :=
  permutation_upper _ _ _ [66,36,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10710

theorem m20125_96 : Upper (D 8) (R 8) [66,36,24,160,96] 13 :=
  permutation_upper _ _ _ [66,36,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10715

theorem m20125_129 : Upper (D 8) (R 8) [66,36,24,160,129] 13 :=
  permutation_upper _ _ _ [66,36,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10720

def r20125 : Route 9 := (fun mask => (mask,id))

def c20125 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20125 : Upper (D 8) (R 8) [66,36,24,160] 13 := by
  apply FastRouting.sound _ _ [66,36,24,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20125 c20125
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20125_33
  · exact m20125_65
  · exact m20125_96
  · exact m20125_129
  · exact u10726
  · exact u10727
  · exact u10728
  · exact u10729
  · exact u10730
  · exact u10731

def b20126 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 28 200 433 417 481 417 417), lower := (rows 67 38 28 200 16 32 64 128 256), losses := [] }

theorem u20126 : Upper (D 8) (R 8) [66,36,24,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20127_33 : Upper (D 8) (R 8) [66,36,24,257,33] 13 :=
  permutation_upper _ _ _ [66,36,24,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10705

theorem m20127_65 : Upper (D 8) (R 8) [66,36,24,257,65] 13 :=
  permutation_upper _ _ _ [66,36,24,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10711

theorem m20127_96 : Upper (D 8) (R 8) [66,36,24,257,96] 13 :=
  permutation_upper _ _ _ [66,36,24,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10716

theorem m20127_129 : Upper (D 8) (R 8) [66,36,24,257,129] 13 :=
  permutation_upper _ _ _ [66,36,24,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10722

theorem m20127_160 : Upper (D 8) (R 8) [66,36,24,257,160] 13 :=
  permutation_upper _ _ _ [66,36,24,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10728

theorem m20127_192 : Upper (D 8) (R 8) [66,36,24,257,192] 13 :=
  permutation_upper _ _ _ [66,36,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10732

def r20127 : Route 9 := (fun mask => (mask,id))

def c20127 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20127 : Upper (D 8) (R 8) [66,36,24,257] 13 := by
  apply FastRouting.sound _ _ [66,36,24,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20127 c20127
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20127_33
  · exact m20127_65
  · exact m20127_96
  · exact m20127_129
  · exact m20127_160
  · exact m20127_192

theorem m20128_33 : Upper (D 8) (R 8) [66,36,24,288,33] 13 :=
  permutation_upper _ _ _ [66,36,24,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10706

theorem m20128_65 : Upper (D 8) (R 8) [66,36,24,288,65] 13 :=
  permutation_upper _ _ _ [66,36,24,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10712

theorem m20128_96 : Upper (D 8) (R 8) [66,36,24,288,96] 13 :=
  permutation_upper _ _ _ [66,36,24,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10717

theorem m20128_129 : Upper (D 8) (R 8) [66,36,24,288,129] 13 :=
  permutation_upper _ _ _ [66,36,24,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10723

theorem m20128_160 : Upper (D 8) (R 8) [66,36,24,288,160] 13 :=
  permutation_upper _ _ _ [66,36,24,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10729

theorem m20128_192 : Upper (D 8) (R 8) [66,36,24,288,192] 13 :=
  permutation_upper _ _ _ [66,36,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10733

def r20128 : Route 9 := (fun mask => (mask,id))

def c20128 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20128 : Upper (D 8) (R 8) [66,36,24,288] 13 := by
  apply FastRouting.sound _ _ [66,36,24,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20128 c20128
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20128_33
  · exact m20128_65
  · exact m20128_96
  · exact m20128_129
  · exact m20128_160
  · exact m20128_192

def b20129 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 28 328 177 161 225 161 417), lower := (rows 67 38 28 328 16 32 64 128 256), losses := [] }

theorem u20129 : Upper (D 8) (R 8) [66,36,24,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20130_33 : Upper (D 8) (R 8) [66,36,24,384,33] 13 :=
  permutation_upper _ _ _ [66,36,24,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10708

theorem m20130_65 : Upper (D 8) (R 8) [66,36,24,384,65] 13 :=
  permutation_upper _ _ _ [66,36,24,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10713

theorem m20130_96 : Upper (D 8) (R 8) [66,36,24,384,96] 13 :=
  permutation_upper _ _ _ [66,36,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10718

theorem m20130_129 : Upper (D 8) (R 8) [66,36,24,384,129] 13 :=
  permutation_upper _ _ _ [66,36,24,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10725

theorem m20130_160 : Upper (D 8) (R 8) [66,36,24,384,160] 13 :=
  permutation_upper _ _ _ [66,36,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10731

theorem m20130_192 : Upper (D 8) (R 8) [66,36,24,384,192] 13 :=
  permutation_upper _ _ _ [66,36,24,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10734

def r20130 : Route 9 := (fun mask => (mask,id))

def c20130 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20130 : Upper (D 8) (R 8) [66,36,24,384] 13 := by
  apply FastRouting.sound _ _ [66,36,24,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20130 c20130
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20130_33
  · exact m20130_65
  · exact m20130_96
  · exact m20130_129
  · exact m20130_160
  · exact m20130_192

def b20131 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 25 504 488 488 488 488), lower := (rows 67 38 133 25 16 32 64 128 256), losses := [] }

theorem u20131 : Upper (D 8) (R 8) [66,36,129,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20132 : PairBound 9 := { available := 504, camps := [{ cop := 3, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 41 504 504 504 504 504), lower := (rows 67 38 133 41 16 32 64 128 256), losses := [] }

theorem u20132 : Upper (D 8) (R 8) [66,36,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20133_9 : Upper (D 8) (R 8) [66,36,129,48,9] 13 :=
  permutation_upper _ _ _ [66,36,129,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10735

theorem m20133_33 : Upper (D 8) (R 8) [66,36,129,48,33] 13 :=
  permutation_upper _ _ _ [66,36,129,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10745

def r20133 : Route 9 := (fun mask => (mask,id))

def c20133 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u20133 : Upper (D 8) (R 8) [66,36,129,48] 13 := by
  apply FastRouting.sound _ _ [66,36,129,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r20133 c20133
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20133_9
  · exact m20133_33
  · exact u10755
  · exact u10756
  · exact u10757
  · exact u10758
  · exact u10759
  · exact u10760
  · exact u10761
  · exact u10762
  · exact u10763
  · exact u10764
  · exact u10765
  · exact u10766
  · exact u10767

def b20134 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 133 73 440 440 504 440 440), lower := (rows 67 38 133 73 16 32 64 128 256), losses := [] }

theorem u20134 : Upper (D 8) (R 8) [66,36,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20135_9 : Upper (D 8) (R 8) [66,36,129,80,9] 13 :=
  permutation_upper _ _ _ [66,36,129,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10736

theorem m20135_33 : Upper (D 8) (R 8) [66,36,129,80,33] 13 :=
  permutation_upper _ _ _ [66,36,129,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10746

theorem m20135_40 : Upper (D 8) (R 8) [66,36,129,80,40] 13 :=
  permutation_upper _ _ _ [66,36,129,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10757

def r20135 : Route 9 := (fun mask => (mask,id))

def c20135 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u20135 : Upper (D 8) (R 8) [66,36,129,80] 13 := by
  apply FastRouting.sound _ _ [66,36,129,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r20135 c20135
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20135_9
  · exact m20135_33
  · exact m20135_40
  · exact u10773
  · exact u10774
  · exact u10775
  · exact u10776
  · exact u10777
  · exact u10778
  · exact u10779

theorem m20136_9 : Upper (D 8) (R 8) [66,36,129,96,9] 13 :=
  permutation_upper _ _ _ [66,36,129,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10737

theorem m20136_33 : Upper (D 8) (R 8) [66,36,129,96,33] 13 :=
  permutation_upper _ _ _ [66,36,129,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10747

theorem m20136_40 : Upper (D 8) (R 8) [66,36,129,96,40] 13 :=
  permutation_upper _ _ _ [66,36,129,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10758

def r20136 : Route 9 := (fun mask => (mask,id))

def c20136 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u20136 : Upper (D 8) (R 8) [66,36,129,96] 13 := by
  apply FastRouting.sound _ _ [66,36,129,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r20136 c20136
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20136_9
  · exact m20136_33
  · exact m20136_40
  · exact u10780
  · exact u10781
  · exact u10782
  · exact u10783
  · exact u10784
  · exact u10785
  · exact u10786

def b20137 : PairBound 9 := { available := 376, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 133 137 376 376 376 504 376), lower := (rows 67 38 133 137 16 32 64 128 256), losses := [] }

theorem u20137 : Upper (D 8) (R 8) [66,36,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20138_9 : Upper (D 8) (R 8) [66,36,129,144,9] 13 :=
  permutation_upper _ _ _ [66,36,129,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10738

theorem m20138_33 : Upper (D 8) (R 8) [66,36,129,144,33] 13 :=
  permutation_upper _ _ _ [66,36,129,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10748

theorem m20138_40 : Upper (D 8) (R 8) [66,36,129,144,40] 13 :=
  permutation_upper _ _ _ [66,36,129,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10760

theorem m20138_65 : Upper (D 8) (R 8) [66,36,129,144,65] 13 :=
  permutation_upper _ _ _ [66,36,129,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10768

theorem m20138_72 : Upper (D 8) (R 8) [66,36,129,144,72] 13 :=
  permutation_upper _ _ _ [66,36,129,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10774

theorem m20138_96 : Upper (D 8) (R 8) [66,36,129,144,96] 13 :=
  permutation_upper _ _ _ [66,36,129,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10781

def r20138 : Route 9 := (fun mask => (mask,id))

def c20138 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u20138 : Upper (D 8) (R 8) [66,36,129,144] 13 := by
  apply FastRouting.sound _ _ [66,36,129,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r20138 c20138
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20138_9
  · exact m20138_33
  · exact m20138_40
  · exact m20138_65
  · exact m20138_72
  · exact m20138_96
  · exact u10790
  · exact u10791
  · exact u10792
  · exact u10793

theorem m20139_9 : Upper (D 8) (R 8) [66,36,129,160,9] 13 :=
  permutation_upper _ _ _ [66,36,129,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10739

theorem m20139_33 : Upper (D 8) (R 8) [66,36,129,160,33] 13 :=
  permutation_upper _ _ _ [66,36,129,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10749

theorem m20139_40 : Upper (D 8) (R 8) [66,36,129,160,40] 13 :=
  permutation_upper _ _ _ [66,36,129,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10761

theorem m20139_65 : Upper (D 8) (R 8) [66,36,129,160,65] 13 :=
  permutation_upper _ _ _ [66,36,129,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10769

theorem m20139_72 : Upper (D 8) (R 8) [66,36,129,160,72] 13 :=
  permutation_upper _ _ _ [66,36,129,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10775

theorem m20139_96 : Upper (D 8) (R 8) [66,36,129,160,96] 13 :=
  permutation_upper _ _ _ [66,36,129,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10782

def r20139 : Route 9 := (fun mask => (mask,id))

def c20139 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u20139 : Upper (D 8) (R 8) [66,36,129,160] 13 := by
  apply FastRouting.sound _ _ [66,36,129,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r20139 c20139
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20139_9
  · exact m20139_33
  · exact m20139_40
  · exact m20139_65
  · exact m20139_72
  · exact m20139_96
  · exact u10794
  · exact u10795
  · exact u10796
  · exact u10797

theorem m20140_9 : Upper (D 8) (R 8) [66,36,129,192,9] 13 :=
  permutation_upper _ _ _ [66,36,129,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10740

theorem m20140_33 : Upper (D 8) (R 8) [66,36,129,192,33] 13 :=
  permutation_upper _ _ _ [66,36,129,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10750

theorem m20140_40 : Upper (D 8) (R 8) [66,36,129,192,40] 13 :=
  permutation_upper _ _ _ [66,36,129,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10762

def r20140 : Route 9 := (fun mask => (mask,id))

def c20140 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20140 : Upper (D 8) (R 8) [66,36,129,192] 13 := by
  apply FastRouting.sound _ _ [66,36,129,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r20140 c20140
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20140_9
  · exact m20140_33
  · exact m20140_40
  · exact u10798
  · exact u10799
  · exact u10800

def b20141 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 265 248 248 248 248 504), lower := (rows 67 38 133 265 16 32 64 128 256), losses := [] }

theorem u20141 : Upper (D 8) (R 8) [66,36,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20142_9 : Upper (D 8) (R 8) [66,36,129,272,9] 13 :=
  permutation_upper _ _ _ [66,36,129,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10741

theorem m20142_33 : Upper (D 8) (R 8) [66,36,129,272,33] 13 :=
  permutation_upper _ _ _ [66,36,129,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10751

theorem m20142_40 : Upper (D 8) (R 8) [66,36,129,272,40] 13 :=
  permutation_upper _ _ _ [66,36,129,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10764

theorem m20142_65 : Upper (D 8) (R 8) [66,36,129,272,65] 13 :=
  permutation_upper _ _ _ [66,36,129,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10770

theorem m20142_72 : Upper (D 8) (R 8) [66,36,129,272,72] 13 :=
  permutation_upper _ _ _ [66,36,129,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10777

theorem m20142_96 : Upper (D 8) (R 8) [66,36,129,272,96] 13 :=
  permutation_upper _ _ _ [66,36,129,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10784

theorem m20142_129 : Upper (D 8) (R 8) [66,36,129,272,129] 13 :=
  permutation_upper _ _ _ [66,36,129,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10787

theorem m20142_136 : Upper (D 8) (R 8) [66,36,129,272,136] 13 :=
  permutation_upper _ _ _ [66,36,129,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10791

theorem m20142_160 : Upper (D 8) (R 8) [66,36,129,272,160] 13 :=
  permutation_upper _ _ _ [66,36,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10795

theorem m20142_192 : Upper (D 8) (R 8) [66,36,129,272,192] 13 :=
  permutation_upper _ _ _ [66,36,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10799

def r20142 : Route 9 := (fun mask => (mask,id))

def c20142 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20142 : Upper (D 8) (R 8) [66,36,129,272] 13 := by
  apply FastRouting.sound _ _ [66,36,129,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20142 c20142
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20142_9
  · exact m20142_33
  · exact m20142_40
  · exact m20142_65
  · exact m20142_72
  · exact m20142_96
  · exact m20142_129
  · exact m20142_136
  · exact m20142_160
  · exact m20142_192

theorem m20143_9 : Upper (D 8) (R 8) [66,36,129,288,9] 13 :=
  permutation_upper _ _ _ [66,36,129,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10742

theorem m20143_33 : Upper (D 8) (R 8) [66,36,129,288,33] 13 :=
  permutation_upper _ _ _ [66,36,129,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10752

theorem m20143_40 : Upper (D 8) (R 8) [66,36,129,288,40] 13 :=
  permutation_upper _ _ _ [66,36,129,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10765

theorem m20143_65 : Upper (D 8) (R 8) [66,36,129,288,65] 13 :=
  permutation_upper _ _ _ [66,36,129,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10771

theorem m20143_72 : Upper (D 8) (R 8) [66,36,129,288,72] 13 :=
  permutation_upper _ _ _ [66,36,129,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10778

theorem m20143_96 : Upper (D 8) (R 8) [66,36,129,288,96] 13 :=
  permutation_upper _ _ _ [66,36,129,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10785

theorem m20143_129 : Upper (D 8) (R 8) [66,36,129,288,129] 13 :=
  permutation_upper _ _ _ [66,36,129,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10788

theorem m20143_136 : Upper (D 8) (R 8) [66,36,129,288,136] 13 :=
  permutation_upper _ _ _ [66,36,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10792

theorem m20143_160 : Upper (D 8) (R 8) [66,36,129,288,160] 13 :=
  permutation_upper _ _ _ [66,36,129,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10796

theorem m20143_192 : Upper (D 8) (R 8) [66,36,129,288,192] 13 :=
  permutation_upper _ _ _ [66,36,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10800

def r20143 : Route 9 := (fun mask => (mask,id))

def c20143 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20143 : Upper (D 8) (R 8) [66,36,129,288] 13 := by
  apply FastRouting.sound _ _ [66,36,129,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20143 c20143
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20143_9
  · exact m20143_33
  · exact m20143_40
  · exact m20143_65
  · exact m20143_72
  · exact m20143_96
  · exact m20143_129
  · exact m20143_136
  · exact m20143_160
  · exact m20143_192

theorem m20144_9 : Upper (D 8) (R 8) [66,36,129,320,9] 13 :=
  permutation_upper _ _ _ [66,36,129,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10743

theorem m20144_33 : Upper (D 8) (R 8) [66,36,129,320,33] 13 :=
  permutation_upper _ _ _ [66,36,129,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10753

theorem m20144_40 : Upper (D 8) (R 8) [66,36,129,320,40] 13 :=
  permutation_upper _ _ _ [66,36,129,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10766

theorem m20144_129 : Upper (D 8) (R 8) [66,36,129,320,129] 13 :=
  permutation_upper _ _ _ [66,36,129,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10789

theorem m20144_136 : Upper (D 8) (R 8) [66,36,129,320,136] 13 :=
  permutation_upper _ _ _ [66,36,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10793

theorem m20144_160 : Upper (D 8) (R 8) [66,36,129,320,160] 13 :=
  permutation_upper _ _ _ [66,36,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10797

def r20144 : Route 9 := (fun mask => (mask,id))

def c20144 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20144 : Upper (D 8) (R 8) [66,36,129,320] 13 := by
  apply FastRouting.sound _ _ [66,36,129,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20144 c20144
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20144_9
  · exact m20144_33
  · exact m20144_40
  · exact m20144_129
  · exact m20144_136
  · exact m20144_160

theorem m20145_9 : Upper (D 8) (R 8) [66,36,129,384,9] 13 :=
  permutation_upper _ _ _ [66,36,129,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10744

theorem m20145_33 : Upper (D 8) (R 8) [66,36,129,384,33] 13 :=
  permutation_upper _ _ _ [66,36,129,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10754

theorem m20145_40 : Upper (D 8) (R 8) [66,36,129,384,40] 13 :=
  permutation_upper _ _ _ [66,36,129,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10767

theorem m20145_65 : Upper (D 8) (R 8) [66,36,129,384,65] 13 :=
  permutation_upper _ _ _ [66,36,129,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10772

theorem m20145_72 : Upper (D 8) (R 8) [66,36,129,384,72] 13 :=
  permutation_upper _ _ _ [66,36,129,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10779

theorem m20145_96 : Upper (D 8) (R 8) [66,36,129,384,96] 13 :=
  permutation_upper _ _ _ [66,36,129,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10786

def r20145 : Route 9 := (fun mask => (mask,id))

def c20145 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20145 : Upper (D 8) (R 8) [66,36,129,384] 13 := by
  apply FastRouting.sound _ _ [66,36,129,384] 13 (by decide) (choices 2) [9,33,40,65,72,96] r20145 c20145
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20145_9
  · exact m20145_33
  · exact m20145_40
  · exact m20145_65
  · exact m20145_72
  · exact m20145_96

def r20146 : Route 9 := (fun mask => (mask,id))

def c20146 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20146 : Upper (D 8) (R 8) [66,36,136,17] 13 := by
  apply FastRouting.sound _ _ [66,36,136,17] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20146 c20146
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10801
  · exact u10802
  · exact u10803
  · exact u10804
  · exact u10805
  · exact u10806
  · exact u10807
  · exact u10808
  · exact u10809
  · exact u10810

def r20147 : Route 9 := (fun mask => (mask,id))

def c20147 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20147 : Upper (D 8) (R 8) [66,36,136,33] 13 := by
  apply FastRouting.sound _ _ [66,36,136,33] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20147 c20147
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10811
  · exact u10812
  · exact u10813
  · exact u10814
  · exact u10815
  · exact u10816
  · exact u10817
  · exact u10818
  · exact u10819
  · exact u10820

def r20148 : Route 9 := (fun mask => (mask,id))

def c20148 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20148 : Upper (D 8) (R 8) [66,36,136,48] 13 := by
  apply FastRouting.sound _ _ [66,36,136,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20148 c20148
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10821
  · exact u10822
  · exact u10823
  · exact u10824
  · exact u10825
  · exact u10826
  · exact u10827
  · exact u10828
  · exact u10829
  · exact u10830

def b20149 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 73 433 433 497 433 433), lower := (rows 67 38 140 73 16 32 64 128 256), losses := [] }

theorem u20149 : Upper (D 8) (R 8) [66,36,136,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20150 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 140 88 433 417 481 417 417), lower := (rows 67 38 140 88 16 32 64 128 256), losses := [] }

theorem u20150 : Upper (D 8) (R 8) [66,36,136,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20151 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 140 104 433 433 497 433 433), lower := (rows 67 38 140 104 16 32 64 128 256), losses := [] }

theorem u20151 : Upper (D 8) (R 8) [66,36,136,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20152 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 137 369 369 369 497 369), lower := (rows 67 38 140 137 16 32 64 128 256), losses := [] }

theorem u20152 : Upper (D 8) (R 8) [66,36,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20153 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 152 369 353 353 481 353), lower := (rows 67 38 140 152 16 32 64 128 256), losses := [] }

theorem u20153 : Upper (D 8) (R 8) [66,36,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20154 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 140 168 369 369 369 497 369), lower := (rows 67 38 140 168 16 32 64 128 256), losses := [] }

theorem u20154 : Upper (D 8) (R 8) [66,36,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20155 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 200 305 305 369 433 305), lower := (rows 67 38 140 200 16 32 64 128 256), losses := [] }

theorem u20155 : Upper (D 8) (R 8) [66,36,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20156 : Route 9 := (fun mask => (mask,id))

def c20156 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20156 : Upper (D 8) (R 8) [66,36,136,257] 13 := by
  apply FastRouting.sound _ _ [66,36,136,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20156 c20156
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10831
  · exact u10832
  · exact u10833
  · exact u10834
  · exact u10835
  · exact u10836

def r20157 : Route 9 := (fun mask => (mask,id))

def c20157 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20157 : Upper (D 8) (R 8) [66,36,136,272] 13 := by
  apply FastRouting.sound _ _ [66,36,136,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20157 c20157
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10837
  · exact u10838
  · exact u10839
  · exact u10840
  · exact u10841
  · exact u10842

def r20158 : Route 9 := (fun mask => (mask,id))

def c20158 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20158 : Upper (D 8) (R 8) [66,36,136,288] 13 := by
  apply FastRouting.sound _ _ [66,36,136,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20158 c20158
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10843
  · exact u10844
  · exact u10845
  · exact u10846
  · exact u10847
  · exact u10848

def b20159 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 140 328 177 177 241 177 433), lower := (rows 67 38 140 328 16 32 64 128 256), losses := [] }

theorem u20159 : Upper (D 8) (R 8) [66,36,136,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u20159
end Delivery.IrregularNine14.P08
